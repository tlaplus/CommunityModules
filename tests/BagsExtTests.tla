---- CONFIG BagsExtTests ----
INIT Init
NEXT Next
=====

---------------------------- MODULE BagsExtTests ----------------------------
EXTENDS Integers, TLC, Bags, BagsExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("BagsExtTests")

-----------------------------------------------------------------------------

ASSUME LET B == SetToBag({1,2}) IN BagAdd(B,2) = B (+) SetToBag({2})
ASSUME LET B == SetToBag({1,2}) IN BagAdd(B,3) = B (+) SetToBag({3})
ASSUME LET B == SetToBag({1,2}) IN BagRemove(B,2) = B (-) SetToBag({2})
ASSUME LET B == SetToBag({1,2}) IN 
           /\ BagRemove(B,3) = B (-) SetToBag({3})
           /\ BagRemove(B,3) = B

-----------------------------------------------------------------------------

ASSUME FoldBag(LAMBDA x,y : x+y, 0, (1:>2) @@ (2:>1) @@ (3:>2)) = 10
ASSUME FoldBag(LAMBDA x,y : x+y, 0, (1:>2) @@ (-2:>1)) = 0

ASSUME SumBag((1:>2) @@ (2:>1) @@ (3:>2)) = 10
ASSUME SumBag((1:>2) @@ (-2:>1)) = 0

ASSUME ProductBag((1:>2) @@ (-2:>1)) = -2
ASSUME ProductBag((1:>2) @@ (0:>1) @@ (10000:>1)) = 0

=============================================================================
