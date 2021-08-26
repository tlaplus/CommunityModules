----------------------------- MODULE FoldsTests ----------------------------
EXTENDS Folds, Integers, FiniteSetsExt, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("FoldsTests")

seq == << 1,2,3,4 >>

ASSUME 
	MapThenFoldSet(
	   LAMBDA x,y: x + y,
	   0,
	   LAMBDA i: seq[i],
	   LAMBDA s: Max(s), 
	   DOMAIN seq) = 10

ASSUME 
	MapThenFoldSet(
	   LAMBDA x,y: x + y,
	   0,
	   LAMBDA i: seq[i],
	   LAMBDA s: Min(s), 
	   DOMAIN seq) = 10

ASSUME 
	MapThenFoldSet(
	   LAMBDA x,y: x * y,
	   1,
	   LAMBDA i: seq[i],
	   LAMBDA s: Max(s), 
	   DOMAIN seq) = 24

ASSUME 
	MapThenFoldSet(
	   LAMBDA x,y: x * y,
	   1,
	   LAMBDA i: seq[i],
	   LAMBDA s: Min(s), 
	   DOMAIN seq) = 24

ASSUME 
	MapThenFoldSet(
	   LAMBDA x,y: x * y,
	   0,
	   LAMBDA i: seq[i],
	   LAMBDA s: Max(s), 
	   DOMAIN seq) = 0

ASSUME 
	MapThenFoldSet(
	   LAMBDA x,y: x * y,
	   0,
	   LAMBDA i: seq[i],
	   LAMBDA s: Min(s), 
	   DOMAIN seq) = 0

ASSUME 
	MapThenFoldSet(
	   LAMBDA x,y: x - y,
	   0,
	   LAMBDA i: seq[i],
	   LAMBDA s: Max(s), 
	   DOMAIN seq) = 2

ASSUME 
	MapThenFoldSet(
	   LAMBDA x,y: x - y,
	   0,
	   LAMBDA i: seq[i],
	   LAMBDA s: Min(s), 
	   DOMAIN seq) = -2

ASSUME 
   AssertError("Attempted to check if the non-enumerable value\n42\nis element of\nSUBSET 42",
	MapThenFoldSet(LAMBDA x,y: x - y, 0, LAMBDA i: seq[i], LAMBDA s: Min(s), 42))

=============================================================================
