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
ASSUME LET B == (1 :> 2) @@ (2 :> 1) IN BagRemoveAll(B,1) = SetToBag({2})

-----------------------------------------------------------------------------

ASSUME LET B == (1 :> 2) @@ (2 :> 1) @@ (3 :> 3)
       IN  MapThenFoldBag(LAMBDA x,y : x \cup y,
                          {},
                          LAMBDA x : {x},
                          LAMBDA S : CHOOSE x \in S : TRUE,
                          B)
         = BagToSet(B)

(***************************************************************************)
(* This operator is a copy of FoldBag in module BagsExt. It serves for     *)
(* testing the Java override of the FoldBag operator. Note that the        *)
(* operator MapThenFoldBag does not have a Java override.                  *)
(***************************************************************************)
TLAFoldBag(op(_,_), base, B) ==
   (************************************************************************)
   (* Fold op over all elements of bag B, starting with value base.        *)
   (*                                                                      *)
   (* Example:                                                             *)
   (*    FoldBag(LAMBDA x,y : x+y,                                         *)
   (*            0,                                                        *)
   (*            (1 :> 2) @@ (2 :> 1) @@ (3 :> 3)) = 13                    *)
   (*    The third argument represents the bag {| 1, 1, 2, 3, 3, 3 |}.     *)
   (************************************************************************)
   MapThenFoldBag(op, base, LAMBDA x: x, LAMBDA S : CHOOSE x \in S : TRUE, B)

ASSUME LET B == (1:>2) @@ (2:>1) @@ (3:>3)
       IN  FoldBag(LAMBDA x,y : x+y, 0, B)
         = TLAFoldBag(LAMBDA x,y : x+y, 0, B)
ASSUME LET B == ({1}:>2) @@ ({-2}:>1) @@ ({3}:>3)
       IN  FoldBag(LAMBDA x,y : x \union y, {}, B)
         = TLAFoldBag(LAMBDA x,y : x \union y, {}, B)

ASSUME FoldBag(LAMBDA x,y : x+y, 0, (1:>2) @@ (2:>1) @@ (3:>3)) = 13
ASSUME FoldBag(LAMBDA x,y : x+y, 0, (1:>2) @@ (-2:>1)) = 0

ASSUME SumBag((1:>2) @@ (2:>1) @@ (3:>2)) = 10
ASSUME SumBag((1:>2) @@ (-2:>1)) = 0

ASSUME ProductBag((1:>2) @@ (-2:>1)) = -2

(***************************************************************************)
(* The two following tests fail without the Java override for FoldBag.     *)
(***************************************************************************)
ASSUME LET B == (1 :> 1000) @@ (-2 :> 500)
       IN FoldBag(LAMBDA x,y : x+y, 0, B) = 0 

ASSUME ProductBag((0 :> 1) @@ (10000 :> 1000)) = 0

=============================================================================
