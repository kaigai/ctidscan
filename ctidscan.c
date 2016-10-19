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
#include "catalog/pg_operator.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "commands/explain.h"
#include "executor/executor.h"
#include "executor/nodeCustom.h"
#include "fmgr.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
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

/* missing declaration in pg_proc.h */
#ifndef TIDGreaterOperator
#define TIDGreaterOperator		2800
#endif
#ifndef TIDLessEqualOperator
#define TIDLessEqualOperator	2801
#endif
#ifndef TIDGreaterEqualOperator
#define TIDGreaterEqualOperator	2802
#endif

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
 * It has few additional internal state. The 'ctid_quals' has list of
 * ExprState for inequality operators that involve ctid system column.
 */
typedef struct {
	CustomScanState	css;
	List		   *ctid_quals;		/* list of ExprState for inequality ops */
	BlockNumber		lower_block;
	BlockNumber		upper_block;
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
static CustomPathMethods	ctidscan_path_methods = {
	"ctidscan",				/* CustomName */
	PlanCtidScanPath,		/* PlanCustomPath */
#if PG_VERSION_NUM < 90600
	NULL,					/* TextOutCustomPath */
#endif
};

static CustomScanMethods	ctidscan_scan_methods = {
	"ctidscan",				/* CustomName */
	CreateCtidScanState,	/* CreateCustomScanState */
#if PG_VERSION_NUM < 90600
	NULL,					/* TextOutCustomScan */
#endif
};

static CustomExecMethods	ctidscan_exec_methods = {
	"ctidscan",				/* CustomName */
	BeginCtidScan,			/* BeginCustomScan */
	ExecCtidScan,			/* ExecCustomScan */
	EndCtidScan,			/* EndCustomScan */
	ReScanCtidScan,			/* ReScanCustomScan */
	NULL,					/* MarkPosCustomScan */
	NULL,					/* RestrPosCustomScan */
#if PG_VERSION_NUM >= 90600
	NULL,					/* EstimateDSMCustomScan */
	NULL,					/* InitializeDSMCustomScan */
	NULL,					/* InitializeWorkerCustomScan */
#endif
	ExplainCtidScan,		/* ExplainCustomScan */
};

#define IsCTIDVar(node,rtindex)											\
	((node) != NULL &&													\
	 IsA((node), Var) &&												\
	 ((Var *) (node))->varno == (rtindex) &&							\
	 ((Var *) (node))->varattno == SelfItemPointerAttributeNumber &&	\
	 ((Var *) (node))->varlevelsup == 0)

/*
 * CTidQualFromExpr
 *
 * It checks whether the given restriction clauses enables to determine
 * the zone to be scanned, or not. If one or more restriction clauses are
 * available, it returns a list of them, or NIL elsewhere.
 * The caller can consider all the conditions are chained with AND-
 * boolean operator, so all the operator works for narrowing down the
 * scope of custom tid scan.
 */
static List *
CTidQualFromExpr(Node *expr, int varno)
{
	if (is_opclause(expr))
	{
		OpExpr *op = (OpExpr *) expr;
		Node   *arg1;
		Node   *arg2;
		Node   *other = NULL;

		/* only inequality operators are candidate */
		if (op->opno != TIDLessOperator &&
			op->opno != TIDLessEqualOperator &&
			op->opno != TIDGreaterOperator &&
			op->opno != TIDGreaterEqualOperator)
			return NULL;

		if (list_length(op->args) != 2)
			return false;	/* should not happen */

		arg1 = linitial(op->args);
		arg2 = lsecond(op->args);

		if (IsCTIDVar(arg1, varno))
			other = arg2;
		else if (IsCTIDVar(arg2, varno))
			other = arg1;
		else
			return NULL;
		if (exprType(other) != TIDOID)
			return NULL;	/* should not happen */
		/* The other argument must be a pseudoconstant */
		if (!is_pseudo_constant_clause(other))
			return NULL;

		return list_make1(copyObject(op));
	}
	else if (and_clause(expr))
	{
		List	   *rlst = NIL;
		ListCell   *lc;

		foreach(lc, ((BoolExpr *) expr)->args)
		{
			List   *temp = CTidQualFromExpr((Node *) lfirst(lc), varno);

			rlst = list_concat(rlst, temp);
		}
		return rlst;
	}
	return NIL;
}

/*
 * CTidEstimateCosts
 *
 * It estimates cost to scan the target relation according to the given
 * restriction clauses. Its logic to scan relations are almost same as
 * SeqScan doing, because it uses regular heap_getnext(), except for
 * the number of tuples to be scanned if restriction clauses work well.
*/
static void
CTidEstimateCosts(PlannerInfo *root,
				  RelOptInfo *baserel,
				  CustomPath *cpath)
{
	Path	   *path = &cpath->path;
	List	   *ctid_quals = cpath->custom_private;
	ListCell   *lc;
	double		ntuples;
	ItemPointerData ip_min;
	ItemPointerData ip_max;
	bool		has_min_val = false;
	bool		has_max_val = false;
	BlockNumber	num_pages;
	Cost		startup_cost = 0;
	Cost		run_cost = 0;
	Cost		cpu_per_tuple;
	QualCost	qpqual_cost;
	QualCost	ctid_qual_cost;
	double		spc_random_page_cost;

	/* Should only be applied to base relations */
	Assert(baserel->relid > 0);
	Assert(baserel->rtekind == RTE_RELATION);

	/* Mark the path with the correct row estimate */
	if (path->param_info)
		path->rows = path->param_info->ppi_rows;
	else
		path->rows = baserel->rows;

	/* Estimate how many tuples we may retrieve */
	ItemPointerSet(&ip_min, 0, 0);
	ItemPointerSet(&ip_max, MaxBlockNumber, MaxOffsetNumber);
	foreach (lc, ctid_quals)
	{
		OpExpr	   *op = lfirst(lc);
		Oid			opno;
		Node	   *other;

		Assert(is_opclause(op));
		if (IsCTIDVar(linitial(op->args), baserel->relid))
		{
			opno = op->opno;
			other = lsecond(op->args);
		}
		else if (IsCTIDVar(lsecond(op->args), baserel->relid))
		{
			/* To simplifies, we assume as if Var node is 1st argument */
			opno = get_commutator(op->opno);
			other = linitial(op->args);
		}
		else
			elog(ERROR, "could not identify CTID variable");

		if (IsA(other, Const))
		{
			ItemPointer	ip = (ItemPointer)(((Const *) other)->constvalue);

			/*
			 * Just an rough estimation, we don't distinct inequality and
			 * inequality-or-equal operator from scan-size estimation
			 * perspective.
			 */
			switch (opno)
			{
				case TIDLessOperator:
				case TIDLessEqualOperator:
					if (ItemPointerCompare(ip, &ip_max) < 0)
						ItemPointerCopy(ip, &ip_max);
					has_max_val = true;
					break;
				case TIDGreaterOperator:
				case TIDGreaterEqualOperator:
					if (ItemPointerCompare(ip, &ip_min) > 0)
						ItemPointerCopy(ip, &ip_min);
					has_min_val = true;
					break;
				default:
					elog(ERROR, "unexpected operator code: %u", op->opno);
					break;
			}
		}
	}

	/* estimated number of tuples in this relation */
	ntuples = baserel->pages * baserel->tuples;

	if (has_min_val && has_max_val)
	{
		/* case of both side being bounded */
		BlockNumber	bnum_max = BlockIdGetBlockNumber(&ip_max.ip_blkid);
		BlockNumber	bnum_min = BlockIdGetBlockNumber(&ip_min.ip_blkid);

		bnum_max = Min(bnum_max, baserel->pages);
		bnum_min = Max(bnum_min, 0);
		num_pages = Min(bnum_max - bnum_min + 1, 1);
	}
	else if (has_min_val)
	{
		/* case of only lower side being bounded */
		BlockNumber	bnum_max = baserel->pages;
		BlockNumber	bnum_min = BlockIdGetBlockNumber(&ip_min.ip_blkid);

		bnum_min = Max(bnum_min, 0);
		num_pages = Min(bnum_max - bnum_min + 1, 1);
	}
	else if (has_max_val)
	{
		/* case of only upper side being bounded */
		BlockNumber	bnum_max = BlockIdGetBlockNumber(&ip_max.ip_blkid);
		BlockNumber	bnum_min = 0;

		bnum_max = Min(bnum_max, baserel->pages);
		num_pages = Min(bnum_max - bnum_min + 1, 1);
	}
	else
	{
		/*
		 * Just a rough estimation. We assume half of records shall be
		 * read using this restriction clause, but indeterministic until
		 * executor run it actually.
		 */
		num_pages = Max((baserel->pages + 1) / 2, 1);
	}
	ntuples *= ((double) num_pages) / ((double) baserel->pages);

	/*
	 * The TID qual expressions will be computed once, any other baserestrict
	 * quals once per retrieved tuple.
	 */
	cost_qual_eval(&ctid_qual_cost, ctid_quals, root);

	/* fetch estimated page cost for tablespace containing table */
	get_tablespace_page_costs(baserel->reltablespace,
							  &spc_random_page_cost,
							  NULL);

	/* disk costs --- assume each tuple on a different page */
	run_cost += spc_random_page_cost * ntuples;

	/*
	 * Add scanning CPU costs
	 * (logic copied from get_restriction_qual_cost)
	 */
	if (path->param_info)
	{
		/* Include costs of pushed-down clauses */
		cost_qual_eval(&qpqual_cost, path->param_info->ppi_clauses, root);

		qpqual_cost.startup += baserel->baserestrictcost.startup;
		qpqual_cost.per_tuple += baserel->baserestrictcost.per_tuple;
	}
	else
		qpqual_cost = baserel->baserestrictcost;

	/*
	 * We don't decrease cost for the inequality operators, because
	 * it is subset of qpquals and still in.
	 */
	startup_cost += qpqual_cost.startup + ctid_qual_cost.per_tuple;
	cpu_per_tuple = cpu_tuple_cost + qpqual_cost.per_tuple -
		ctid_qual_cost.per_tuple;
	run_cost = cpu_per_tuple * ntuples;

	path->startup_cost = startup_cost;
	path->total_cost = startup_cost + run_cost;
}

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
		List		 *temp;

		if (!IsA(rinfo, RestrictInfo))
			continue;		/* probably should never happen */
		temp = CTidQualFromExpr((Node *) rinfo->clause, baserel->relid);
		ctid_quals = list_concat(ctid_quals, temp);
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

		/*
		 * We don't support pushing join clauses into the quals of a ctidscan,
		 * but it could still have required parameterization due to LATERAL
		 * refs in its tlist.
		 */
		required_outer = baserel->lateral_relids;

		cpath = palloc0(sizeof(CustomPath));
		cpath->path.type = T_CustomPath;
		cpath->path.pathtype = T_CustomScan;
		cpath->path.parent = baserel;
#if PG_VERSION_NUM >= 90600
		cpath->path.pathtarget = baserel->reltarget;
#endif
		cpath->path.param_info
			= get_baserel_parampathinfo(root, baserel, required_outer);
		cpath->flags = CUSTOMPATH_SUPPORT_BACKWARD_SCAN;
		cpath->custom_private = ctid_quals;
		cpath->methods = &ctidscan_path_methods;

		CTidEstimateCosts(root, baserel, cpath);

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
	List		   *ctid_quals = best_path->custom_private;
	CustomScan	   *cscan = makeNode(CustomScan);

	cscan->flags = best_path->flags;
	cscan->methods = &ctidscan_scan_methods;

	/* set scanrelid */
	cscan->scan.scanrelid = rel->relid;
	/* set targetlist as is  */
	cscan->scan.plan.targetlist = tlist;
	/* reduce RestrictInfo list to bare expressions */
	cscan->scan.plan.qual = extract_actual_clauses(clauses, false);
	/* set ctid related quals */
	cscan->custom_exprs = ctid_quals;

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

	/*
	 * In case of custom-scan provider that offers an alternative way
	 * to scan a particular relation, most of the needed initialization,
	 * like relation open or assignment of scan tuple-slot or projection
	 * info, shall be done by the core implementation. So, all we need
	 * to have is initialization of own local properties.
	 */
	ctss->ctid_quals = (List *)
		ExecInitExpr((Expr *)cscan->custom_exprs, &node->ss.ps);
}

/*
 * ReScanCtidScan - A method of CustomScanState; that rewind the current
 * seek position.
 */
static void
ReScanCtidScan(CustomScanState *node)
{
	CtidScanState  *ctss = (CtidScanState *)node;
	HeapScanDesc	scan = ctss->css.ss.ss_currentScanDesc;
	EState		   *estate = node->ss.ps.state;
	ScanDirection	direction = estate->es_direction;
	Relation		relation = ctss->css.ss.ss_currentRelation;
	ExprContext	   *econtext = ctss->css.ss.ps.ps_ExprContext;
	bool			has_ubound = false;
	bool			has_lbound = false;
	ItemPointerData	ip_max;
	ItemPointerData	ip_min;
	ListCell	   *lc;

	/* once close the existing scandesc, if any */
	if (scan)
	{
		heap_endscan(scan);
		scan = ctss->css.ss.ss_currentScanDesc = NULL;
	}

	/* walks on the inequality operators */
	foreach (lc, ctss->ctid_quals)
	{
		FuncExprState  *fexstate = (FuncExprState *) lfirst(lc);
		OpExpr		   *op = (OpExpr *)fexstate->xprstate.expr;
		Node		   *arg1 = linitial(op->args);
		Node		   *arg2 = lsecond(op->args);
		Index			scanrelid;
		Oid				opno;
		ExprState	   *exstate;
		ItemPointer		itemptr;
		bool			isnull;

		scanrelid = ((Scan *)ctss->css.ss.ps.plan)->scanrelid;
		if (IsCTIDVar(arg1, scanrelid))
		{
			exstate = (ExprState *) lsecond(fexstate->args);
			opno = op->opno;
		}
		else if (IsCTIDVar(arg2, scanrelid))
		{
			exstate = (ExprState *) linitial(fexstate->args);
			opno = get_commutator(op->opno);
		}
		else
			elog(ERROR, "could not identify CTID variable");

		itemptr = (ItemPointer)
			DatumGetPointer(ExecEvalExprSwitchContext(exstate,
													  econtext,
													  &isnull,
													  NULL));
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
				if (!has_ubound ||
					ItemPointerCompare(itemptr, &ip_max) <= 0)
				{
					ItemPointerCopy(itemptr, &ip_max);
					has_ubound = true;
				}
				break;

			case TIDLessEqualOperator:
				if (!has_ubound ||
					ItemPointerCompare(itemptr, &ip_max) < 0)
				{
					ItemPointerCopy(itemptr, &ip_max);
					has_ubound = true;
				}
				break;

			case TIDGreaterOperator:
				if (!has_lbound ||
					ItemPointerCompare(itemptr, &ip_min) >= 0)
				{
					ItemPointerCopy(itemptr, &ip_min);
					has_lbound = true;
				}
				break;

			case TIDGreaterEqualOperator:
				if (!has_lbound ||
					ItemPointerCompare(itemptr, &ip_min) > 0)
				{
					ItemPointerCopy(itemptr, &ip_min);
					has_lbound = true;
				}
				break;

			default:
				elog(ERROR, "unsupported operator");
				break;
		}
	}

	/* begin heapscan with the key above */
	scan = heap_beginscan(relation, estate->es_snapshot, 0, NULL);

	/* Seek the starting position, if possible */
	if (direction == ForwardScanDirection && has_lbound)
	{
		BlockNumber	blknum = Min(BlockIdGetBlockNumber(&ip_min.ip_blkid),
								 scan->rs_nblocks - 1);
		scan->rs_startblock = blknum;
	}
	else if (direction == BackwardScanDirection && has_ubound)
	{
		BlockNumber	blknum = Min(BlockIdGetBlockNumber(&ip_max.ip_blkid),
								 scan->rs_nblocks - 1);
		scan->rs_startblock = blknum;
	}

	ctss->lower_block = has_lbound ? BlockIdGetBlockNumber(&ip_min.ip_blkid) : (BlockNumber) 0;
	ctss->upper_block = has_ubound ? BlockIdGetBlockNumber(&ip_max.ip_blkid) : MaxBlockNumber;

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
	HeapScanDesc	scan;
	TupleTableSlot *slot;
	EState		   *estate = node->ss.ps.state;
	ScanDirection	direction = estate->es_direction;
	HeapTuple		tuple;

	if (!ctss->css.ss.ss_currentScanDesc)
		ReScanCtidScan(node);
	scan = ctss->css.ss.ss_currentScanDesc;
	Assert(scan != NULL);

	/*
	 * get the next tuple from the table
	 */
	tuple = heap_getnext(scan, direction);
	if (!HeapTupleIsValid(tuple))
		return NULL;

	if ((scan->rs_cblock < ctss->lower_block) || (ctss->upper_block < scan->rs_cblock))
		return NULL;

	slot = ctss->css.ss.ss_ScanTupleSlot;
	ExecStoreTuple(tuple, slot, scan->rs_cbuf, false);

	return slot;
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
		heap_endscan(ctss->css.ss.ss_currentScanDesc);
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
		context = set_deparse_context_planstate(es->deparse_cxt,
												(Node *) &node->ss.ps,
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

	/* registration of the hook to add alternative path */
	set_rel_pathlist_next = set_rel_pathlist_hook;
	set_rel_pathlist_hook = SetCtidScanPath;
}
