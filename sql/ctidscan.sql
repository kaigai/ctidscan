--
-- Regression Tests for Custom Plan APIs
--

-- construction of test data
SET client_min_messages TO 'warning';

CREATE SCHEMA regtest_custom_scan;

SET search_path TO regtest_custom_scan, public;

CREATE TABLE t1 (
    a   int primary key,
    b   text
);
INSERT INTO t1 (SELECT s, md5(s::text) FROM generate_series(1,400) s);
VACUUM ANALYZE t1;

CREATE TABLE t2 (
    x   int primary key,
    y   text
);
INSERT INTO t2 (SELECT s, md5(s::text)||md5(s::text) FROM generate_series(1,400) s);
VACUUM ANALYZE t2;

RESET client_min_messages;
--
-- Check Plans if no special extension is loaded.
--
EXPLAIN (costs off) SELECT * FROM t1 WHERE a = 40;
EXPLAIN (costs off) SELECT * FROM t1 WHERE b like '%789%';
EXPLAIN (costs off) SELECT * FROM t1 WHERE ctid = '(2,10)'::tid;
EXPLAIN (costs off) SELECT * FROM t1 WHERE ctid BETWEEN '(2,115)'::tid AND '(3,10)'::tid;

--
-- Plan for same query but ctidscan was loaded
--
LOAD '$libdir/ctidscan';
EXPLAIN (costs off) SELECT * FROM t1 WHERE a = 40;
EXPLAIN (costs off) SELECT * FROM t1 WHERE b like '%789%';
EXPLAIN (costs off) SELECT * FROM t1 WHERE ctid = '(2,10)'::tid;
EXPLAIN (costs off) SELECT * FROM t1 WHERE ctid BETWEEN '(2,115)'::tid AND '(3,10)'::tid;
EXPLAIN (costs off) SELECT * FROM t1 JOIN t2 ON t1.ctid = t2.ctid WHERE t1.ctid < '(2,10)'::tid AND t2.ctid > '(1,75)'::tid;

SELECT ctid,* FROM t1 WHERE ctid < '(1,20)'::tid;
SELECT ctid,* FROM t1 WHERE ctid > '(4,0)'::tid;
SELECT ctid,* FROM t1 WHERE ctid BETWEEN '(2,115)'::tid AND '(3,10)'::tid;
SELECT t1.ctid,* FROM t1 JOIN t2 ON t1.ctid = t2.ctid WHERE t1.ctid < '(2,10)'::tid AND t2.ctid > '(1,75)'::tid;

PREPARE p1(tid, tid) AS SELECT ctid,* FROM t1
                        WHERE b like '%abc%' AND ctid BETWEEN $1 AND $2;
EXPLAIN (costs off) EXECUTE p1('(5,0)'::tid, '(10,0)'::tid);
EXPLAIN (costs off) EXECUTE p1('(10,0)'::tid, '(5,0)'::tid);

-- Also, EXPLAIN with none-text format
EXPLAIN (costs off, format xml) EXECUTE p1('(0,0)'::tid, '(5,0)'::tid);

-- Test cleanup
DROP SCHEMA regtest_custom_scan CASCADE;
