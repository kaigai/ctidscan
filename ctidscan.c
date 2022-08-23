/*
 * ctidscan.c
 *
 * A custom-scan provide that utilizes ctid system column within
 * inequality-operators, to skip block reads never referenced.
 *
 * It is designed to demonstrate Custom Scan APIs; that allows to override
 * a part of executor node. This extension focus on a workload that tries
 * to fetch records with tid larger or less than a particular value.
 * In case when inequality operators were given, this module construct
 * a custom scan path that enables to skip records not to be read. Then,
 * if it was the cheapest one, it shall be used to run the query.
 * Custom Scan APIs callbacks this extension when executor tries to fetch
 * underlying records, then it utilizes existing heap_getnext() but seek
 * the records to be read prior to fetching the first record.
 *
 * Portions Copyright (c) 2014, PostgreSQL Global Development Group
 */
#include "postgres.h"
#include "access/relscan.h"
#include "access/sysattr.h"
#include "access/skey.h"
#include "access/tableam.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "commands/explain.h"
#include "executor/executor.h"
#include "executor/nodeCustom.h"
#include "fmgr.h"
#include "miscadmin.h"
#include "nodes/extensible.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/paths.h"
#include "optimizer/pathnode.h"
#include "optimizer/plancat.h"
#include "optimizer/planmain.h"
#include "optimizer/placeholder.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/subselect.h"
#include "parser/parsetree.h"
#include "storage/bufmgr.h"
#include "storage/itemptr.h"
#include "utils/builtins.h"
#include "utils/fmgroids.h"
#include "utils/guc.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/ruleutils.h"
#include "utils/spccache.h"

PG_MODULE_MAGIC;

/*
 * NOTE: We don't use any special data type to save the private data.
 * All we want to save in private fields is expression-list that shall
 * be adjusted by setrefs.c/subselect.c, so we put it on the custom_exprs
 * of CustomScan structure, not custom_private field.
 * Due to the interface contract, only expression nodes are allowed to put
 * on the custom_exprs, and we have to pay attention the core backend may
 * adjust expression items.
 */

/*
 * CtidScanState - state object of ctidscan on executor.
 */
typedef struct {
	CustomScanState	css;
	List	   *ctid_exprs;
	List	   *ctid_opers;
} CtidScanState;

/* static variables */
static bool		enable_ctidscan;
static set_rel_pathlist_hook_type set_rel_pathlist_next = NULL;

/* function declarations */
void	_PG_init(void);

static void SetCtidScanPath(PlannerInfo *root,
							RelOptInfo *rel,
							Index rti,
							RangeTblEntry *rte);
/* CustomPathMethods */
static Plan *PlanCtidScanPath(PlannerInfo *root,
							  RelOptInfo *rel,
							  CustomPath *best_path,
							  List *tlist,
							  List *clauses,
							  List *custom_plans);

/* CustomScanMethods */
static Node *CreateCtidScanState(CustomScan *custom_plan);

/* CustomScanExecMethods */
static void BeginCtidScan(CustomScanState *node, EState *estate, int eflags);
static void ReScanCtidScan(CustomScanState *node);
static TupleTableSlot *ExecCtidScan(CustomScanState *node);
static void EndCtidScan(CustomScanState *node);
static void ExplainCtidScan(CustomScanState *node, List *ancestors,
							ExplainState *es);

/* static table of custom-scan callbacks */
static CustomPathMethods	ctidscan_path_methods;
static CustomScanMethods	ctidscan_scan_methods;
static CustomExecMethods	ctidscan_exec_methods;

#define IsCTIDVar(node,rtindex)											\
	((node) != NULL &&													\
	 IsA((node), Var) &&												\
	 ((Var *) (node))->varno == (rtindex) &&							\
	 ((Var *) (node))->varattno == SelfItemPointerAttributeNumber &&	\
	 ((Var *) (node))->varlevelsup == 0)

/*
 * SetCtidScanPath - entrypoint of the series of custom-scan execution.
 * It adds CustomPath if referenced relation has inequality expressions on
 * the ctid system column.
 */
static void
SetCtidScanPath(PlannerInfo *root, RelOptInfo *baserel,
				Index rtindex, RangeTblEntry *rte)
{
	char			relkind;
	ListCell	   *lc;
	List		   *ctid_quals = NIL;

	/* only plain relations are supported */
	if (rte->rtekind != RTE_RELATION)
		return;
	relkind = get_rel_relkind(rte->relid);
	if (relkind != RELKIND_RELATION &&
		relkind != RELKIND_MATVIEW &&
		relkind != RELKIND_TOASTVALUE)
		return;

	/*
	 * NOTE: Unlike built-in execution path, always we can have core path
	 * even though ctid scan is not available. So, simply, we don't add
	 * any paths, instead of adding disable_cost.
	 */
	if (!enable_ctidscan)
		return;

	/* walk on the restrict info */
	foreach (lc, baserel->baserestrictinfo)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		if (is_opclause(rinfo->clause))
		{
			OpExpr *op = (OpExpr *) rinfo->clause;

			if (op->opno == TIDLessOperator ||
				op->opno == TIDLessEqOperator ||
				op->opno == TIDGreaterOperator ||
				op->opno == TIDGreaterEqOperator)
				ctid_quals = lappend(ctid_quals, rinfo);
		}
	}

	/*
	 * OK, it is case when a part of restriction clause makes sense to
	 * reduce number of tuples, so we will add a custom scan path being
	 * provided by this module.
	 */
	if (ctid_quals != NIL)
	{
		CustomPath *cpath;
		Relids		required_outer;
		ParamPathInfo *param_info;

		/*
		 * We don't support pushing join clauses into the quals of a ctidscan,
		 * but it could still have required parameterization due to LATERAL
		 * refs in its tlist.
		 */
		required_outer = baserel->lateral_relids;
		param_info = get_baserel_parampathinfo(root, baserel, required_outer);

		cpath = palloc0(sizeof(CustomPath));
		cpath->path.type = T_CustomPath;
		cpath->path.pathtype = T_CustomScan;
		cpath->path.parent = baserel;
		cpath->path.pathtarget = baserel->reltarget;
		cpath->path.param_info = param_info;
		cpath->flags = CUSTOMPATH_SUPPORT_BACKWARD_SCAN;
		cpath->custom_private = ctid_quals;
		cpath->methods = &ctidscan_path_methods;

		cost_tidscan(&cpath->path, root, baserel, ctid_quals, param_info);

		add_path(baserel, &cpath->path);
	}
}

/*
 * PlanCtidScanPlan - A method of CustomPath; that populate a custom
 * object being delivered from CustomScan type, according to the supplied
 * CustomPath object.
 */
static Plan *
PlanCtidScanPath(PlannerInfo *root,
				 RelOptInfo *rel,
				 CustomPath *best_path,
				 List *tlist,
				 List *clauses,
				 List *custom_plans)
{
	CustomScan *cscan = makeNode(CustomScan);
	List	   *ctid_quals = best_path->custom_private;

	cscan->flags = best_path->flags;
	cscan->methods = &ctidscan_scan_methods;

	/* set scanrelid */
	cscan->scan.scanrelid = rel->relid;
	/* set targetlist as is  */
	cscan->scan.plan.targetlist = tlist;
	/* full WHERE-clause */
	cscan->scan.plan.qual = extract_actual_clauses(clauses, false);
	/* set ctid related quals */
	cscan->custom_exprs = extract_actual_clauses(ctid_quals, false);

	return &cscan->scan.plan;
}

/*
 * CreateCtidScanState - A method of CustomScan; that populate a custom
 * object being delivered from CustomScanState type, according to the
 * supplied CustomPath object.
 */
static Node *
CreateCtidScanState(CustomScan *custom_plan)
{
	CtidScanState  *ctss = palloc0(sizeof(CtidScanState));

	NodeSetTag(ctss, T_CustomScanState);
	ctss->css.flags = custom_plan->flags;
	ctss->css.methods = &ctidscan_exec_methods;

	return (Node *)&ctss->css;
}

/*
 * BeginCtidScan - A method of CustomScanState; that initializes
 * the supplied CtidScanState object, at beginning of the executor.
 */
static void
BeginCtidScan(CustomScanState *node, EState *estate, int eflags)
{
	CtidScanState  *ctss = (CtidScanState *) node;
	CustomScan	   *cscan = (CustomScan *) node->ss.ps.plan;
	Relation		relation = ctss->css.ss.ss_currentRelation;
	ListCell	   *lc;
	List		   *ctid_exprs = NIL;
	List		   *ctid_opers = NIL;

	foreach (lc, cscan->custom_exprs)
	{
		OpExpr	   *op = lfirst(lc);
		Expr	   *arg1 = linitial(op->args);
		Expr	   *arg2 = lsecond(op->args);
		ExprState  *estate;
		Oid			opno;

		if (IsCTIDVar(arg1, cscan->scan.scanrelid))
		{
			estate = ExecInitExpr(arg2, &ctss->css.ss.ps);
			opno = op->opno;
		}
		else if (IsCTIDVar(arg2, cscan->scan.scanrelid))
		{
			estate = ExecInitExpr(arg1, &ctss->css.ss.ps);
			opno = get_commutator(op->opno);
		}
		else
			elog(ERROR, "could not identify CTID variable");

		ctid_exprs = lappend(ctid_exprs, estate);
		ctid_opers = lappend_oid(ctid_opers, opno);
	}
	ctss->ctid_exprs = ctid_exprs;
	ctss->ctid_opers = ctid_opers;

	/* setup scan-slot and projection again */
	ExecInitScanTupleSlot(estate, &ctss->css.ss,
						  RelationGetDescr(relation),
						  table_slot_callbacks(relation));
	ExecAssignScanProjectionInfoWithVarno(&ctss->css.ss,
										  cscan->scan.scanrelid);
	/* setup WHERE-clause again */
	ctss->css.ss.ps.qual = ExecInitQual(cscan->scan.plan.qual, &ctss->css.ss.ps);
}

/*
 * ReScanCtidScan - A method of CustomScanState; that rewind the current
 * seek position.
 */
static void
ReScanCtidScan(CustomScanState *node)
{
	CtidScanState  *ctss = (CtidScanState *)node;
	TableScanDesc	scan = ctss->css.ss.ss_currentScanDesc;
	EState		   *estate = node->ss.ps.state;
	Relation		relation = ctss->css.ss.ss_currentRelation;
	ExprContext	   *econtext = ctss->css.ss.ps.ps_ExprContext;
	ItemPointerData	ip_max;
	ItemPointerData	ip_min;
	ListCell	   *lc1, *lc2;

	/* once close the existing scandesc, if any */
	if (scan)
	{
		table_endscan(scan);
		scan = ctss->css.ss.ss_currentScanDesc = NULL;
	}

	/* walks on the inequality operators */
	ItemPointerSet(&ip_min, 0, FirstOffsetNumber);
	ItemPointerSet(&ip_max, MaxBlockNumber, MaxOffsetNumber);
	forboth (lc1, ctss->ctid_exprs,
			 lc2, ctss->ctid_opers)
	{
		ExprState  *estate = lfirst(lc1);
		Oid			opno = lfirst_oid(lc2);
		bool		isnull;
		ItemPointer	itemptr;

		itemptr = (ItemPointer)
			DatumGetPointer(ExecEvalExprSwitchContext(estate, econtext, &isnull));
		if (isnull)
		{
			/*
			 * Whole of the restriction clauses chained with AND- boolean
			 * operators because false, if one of the clauses has NULL result.
			 * So, we can immediately break the evaluation to inform caller
			 * it does not make sense to scan any more.
			 * In this case, scandesc is kept to NULL.
			 */
			return;
		}

		switch (opno)
		{
			case TIDLessOperator:
				if (ItemPointerCompare(itemptr, &ip_max) <= 0)
					ItemPointerCopy(itemptr, &ip_max);
				break;
			case TIDLessEqOperator:
				if (ItemPointerCompare(itemptr, &ip_max) < 0)
					ItemPointerCopy(itemptr, &ip_max);
				break;
			case TIDGreaterOperator:
				if (ItemPointerCompare(itemptr, &ip_min) >= 0)
					ItemPointerCopy(itemptr, &ip_min);
				break;
			case TIDGreaterEqOperator:
				if (ItemPointerCompare(itemptr, &ip_min) > 0)
					ItemPointerCopy(itemptr, &ip_min);
				break;
			default:
				elog(ERROR, "unsupported operator");
				break;
		}
	}
	/* begin table scan with ctid range */
	scan = table_beginscan_tidrange(relation, estate->es_snapshot, &ip_min, &ip_max);
	ctss->css.ss.ss_currentScanDesc = scan;
}

/*
 * CTidAccessCustomScan
 *
 * Access method of ExecCtidScan below. It fetches a tuple from the underlying
 * heap scan that was  started from the point according to the tid clauses.
 */
static TupleTableSlot *
CTidAccessCustomScan(CustomScanState *node)
{
	CtidScanState  *ctss = (CtidScanState *) node;
	TupleTableSlot *slot = ctss->css.ss.ss_ScanTupleSlot;
	EState		   *estate = node->ss.ps.state;
	ScanDirection	direction = estate->es_direction;
	TableScanDesc	scan;

	if (!ctss->css.ss.ss_currentScanDesc)
		ReScanCtidScan(node);
	scan = ctss->css.ss.ss_currentScanDesc;
	if (scan && table_scan_getnextslot(scan, direction, slot))
		return slot;
	return NULL;
}

static bool
CTidRecheckCustomScan(CustomScanState *node, TupleTableSlot *slot)
{
	return true;
}

/*
 * ExecCtidScan - A method of CustomScanState; that fetches a tuple
 * from the relation, if exist anymore.
 */
static TupleTableSlot *
ExecCtidScan(CustomScanState *node)
{
	return ExecScan(&node->ss,
					(ExecScanAccessMtd) CTidAccessCustomScan,
					(ExecScanRecheckMtd) CTidRecheckCustomScan);
}

/*
 * CTidEndCustomScan - A method of CustomScanState; that closes heap and
 * scan descriptor, and release other related resources.
 */
static void
EndCtidScan(CustomScanState *node)
{
	CtidScanState  *ctss = (CtidScanState *)node;

	if (ctss->css.ss.ss_currentScanDesc)
		table_endscan(ctss->css.ss.ss_currentScanDesc);
}

/*
 * ExplainCtidScan - A method of CustomScanState; that shows extra info
 * on EXPLAIN command.
 */
static void
ExplainCtidScan(CustomScanState *node, List *ancestors, ExplainState *es)
{
	CtidScanState  *ctss = (CtidScanState *) node;
	CustomScan	   *cscan = (CustomScan *) ctss->css.ss.ps.plan;

	/* logic copied from show_qual and show_expression */
	if (cscan->custom_exprs)
	{
		bool	useprefix = es->verbose;
		Node   *qual;
		List   *context;
		char   *exprstr;

		/* Convert AND list to explicit AND */
		qual = (Node *) make_ands_explicit(cscan->custom_exprs);

		/* Set up deparsing context */
		context = set_deparse_context_plan(es->deparse_cxt,
										   (Plan *)cscan,
										   ancestors);

		/* Deparse the expression */
		exprstr = deparse_expression(qual, context, useprefix, false);

		/* And add to es->str */
		ExplainPropertyText("ctid quals", exprstr, es);
	}
}

/*
 * Entrypoint of this extension
 */
void
_PG_init(void)
{
	DefineCustomBoolVariable("enable_ctidscan",
							 "Enables the planner's use of ctid-scan plans.",
							 NULL,
							 &enable_ctidscan,
							 true,
							 PGC_USERSET,
							 GUC_NOT_IN_SAMPLE,
							 NULL, NULL, NULL);
	/* path methods */
	memset(&ctidscan_path_methods, 0, sizeof(ctidscan_path_methods));
	ctidscan_path_methods.CustomName		= "ctidscan";
	ctidscan_path_methods.PlanCustomPath	= PlanCtidScanPath;

	/* plan methods */
	memset(&ctidscan_scan_methods, 0, sizeof(ctidscan_scan_methods));
	ctidscan_scan_methods.CustomName		= "ctidscan";
	ctidscan_scan_methods.CreateCustomScanState = CreateCtidScanState;

	/* exec methods */
	memset(&ctidscan_exec_methods, 0, sizeof(ctidscan_exec_methods));
	ctidscan_exec_methods.CustomName		= "ctidscan";
	ctidscan_exec_methods.BeginCustomScan	= BeginCtidScan;
	ctidscan_exec_methods.ExecCustomScan	= ExecCtidScan;
	ctidscan_exec_methods.EndCustomScan		= EndCtidScan;
	ctidscan_exec_methods.ReScanCustomScan	= ReScanCtidScan;
	ctidscan_exec_methods.ExplainCustomScan	= ExplainCtidScan;
	
	/* registration of the hook to add alternative path */
	set_rel_pathlist_next = set_rel_pathlist_hook;
	set_rel_pathlist_hook = SetCtidScanPath;
}
