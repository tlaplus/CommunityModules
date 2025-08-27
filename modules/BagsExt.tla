------------------------------ MODULE BagsExt ------------------------------
(***************************************************************************)
(* Additional operators on bags (multisets).                               *)
(*                                                                         *)
(* Bags represent multisets - collections where elements can appear        *)
(* multiple times. In TLA+, bags are represented as functions from         *)
(* elements to positive natural numbers, where bag[x] gives the            *)
(* multiplicity (count) of element x.                                      *)
(*                                                                         *)
(* This module extends the standard Bags module with:                      *)
(*   - Element manipulation (add, remove individual/all occurrences)       *)
(*   - Folding operations (generalized aggregation over bag elements)      *)
(*   - Arithmetic operations (sum, product of bag elements)                *)
(*                                                                         *)
(* Example bag representation:                                             *)
(*   The bag {| 1, 1, 2, 3, 3, 3 |} is represented as:                     *)
(*   (1 :> 2) @@ (2 :> 1) @@ (3 :> 3)                                      *)
(***************************************************************************)

LOCAL INSTANCE Bags
LOCAL INSTANCE Integers
LOCAL INSTANCE Folds

(***************************************************************************)
(* Add one occurrence of element x to bag B.                               *)
(*                                                                         *)
(* Increases the multiplicity of x by 1. If x is not in the bag,           *)
(* adds it with multiplicity 1.                                            *)
(*                                                                         *)
(* This is equivalent to B (+) SetToBag({x}.                               *)
(*                                                                         *)
(* Examples:                                                               *)
(*   BagAdd((1 :> 2) @@ (2 :> 1), 1) = (1 :> 3) @@ (2 :> 1)                *)
(*   BagAdd((1 :> 2) @@ (2 :> 1), 3) = (1 :> 2) @@ (2 :> 1) @@ (3 :> 1)    *)
(***************************************************************************)
BagAdd(B, x) ==
   IF x \in DOMAIN B
   THEN [e \in DOMAIN B |-> IF e=x THEN B[e]+1 ELSE B[e]]
   ELSE [e \in DOMAIN B \union {x} |-> IF e=x THEN 1 ELSE B[e]]

(***************************************************************************)
(* Remove one occurrence of element x from bag B.                          *)
(*                                                                         *)
(* Decreases the multiplicity of x by 1. If x has multiplicity 1,          *)
(* removes it entirely from the bag. If x is not in the bag, equals        *)
(* the bag unchanged.                                                      *)
(*                                                                         *)
(* This is equivalent to B (-) SetToBag({x}).                              *)
(*                                                                         *)
(* Examples:                                                               *)
(*   BagRemove((1 :> 2) @@ (2 :> 1), 1) = (1 :> 1) @@ (2 :> 1)             *)
(*   BagRemove((1 :> 1) @@ (2 :> 1), 1) = (2 :> 1)                         *)
(*   BagRemove((1 :> 2) @@ (2 :> 1), 3) = (1 :> 2) @@ (2 :> 1)             *)
(***************************************************************************)
BagRemove(B,x) ==
   IF x \in DOMAIN B
   THEN IF B[x] = 1
        THEN [e \in DOMAIN B \ {x} |-> B[e]]
        ELSE [e \in DOMAIN B |-> IF e=x THEN B[e]-1 ELSE B[e]]
   ELSE B

(***************************************************************************)
(* Remove all occurrences of element x from bag B.                         *)
(*                                                                         *)
(* Completely removes element x from the bag, regardless of its            *)
(* multiplicity. If x is not in the bag, returns the bag unchanged.        *)
(*                                                                         *)
(* Examples:                                                               *)
(*   BagRemoveAll((1 :> 3) @@ (2 :> 1), 1) = (2 :> 1)                      *)
(*   BagRemoveAll((1 :> 3) @@ (2 :> 1), 3) = (1 :> 3) @@ (2 :> 1)          *)
(***************************************************************************)
BagRemoveAll(B,x) ==
   [e \in DOMAIN B \ {x} |-> B[e]]
 
(***********************************************************************)
(* Fold operation op over the images through f of all elements of bag  *)
(* B, starting from base. The parameter choose indicates the order in  *)
(* which elements of the bag are processed; all replicas of an element *)
(* are processed consecutively.                                        *)
(*                                                                     *)
(* Examples:                                                           *)
(*    MapThenFoldBag(LAMBDA x,y : x+y,                                 *)
(*                   0,                                                *)
(*                   LAMBDA x: 1,                                      *)
(*                   LAMBDA B : CHOOSE x \in DOMAIN B : TRUE,          *)
(*                   (1 :> 2) @@ (2 :> 1) @@ (3 :> 3)) = 6             *)
(*                                                                     *)
(*    MapThenFoldBag(LAMBDA x,y : x \o y,                              *)
(*                   << >>,                                            *)
(*                   LAMBDA x: << x >>,                                *)
(*                   LAMBDA S: CHOOSE x \in S : \A y \in S : x <= y,   *)
(*                   (1 :> 2) @@ (2 :> 1) @@ (3 :> 3))                 *)
(*                 = <<1,1,2,3,3,3>>                                   *)
(*                                                                     *)
(*    The fifth argument represents the bag {| 1, 1, 2, 3, 3, 3 |}.    *)
(*    The first example counts the elements of the bag.                *)
(*    The second example computes a sorted sequence of all elements    *)
(*    of the bag. It is brittle because concatenation of sequences is  *)
(*    non-commutative, and the result therefore relies on the          *)
(*    definition of MapThenFoldSet.                                    *)
(***********************************************************************)
 MapThenFoldBag(op(_,_), base, f(_), choose(_), B) ==
    LET handle(x) ==  \* handle all occurrences of x in B
        LET pow[n \in Nat \ {0}] ==
            op(IF n=1 THEN base ELSE pow[n-1], f(x))
        IN  pow[B[x]]
    IN  MapThenFoldSet(op, base, handle,
                       LAMBDA S : CHOOSE x \in S : TRUE,
                       DOMAIN B)

(************************************************************************)
(* Fold op over all elements of bag B, starting with value base.        *)
(*                                                                      *)
(* Example:                                                             *)
(*    FoldBag(LAMBDA x,y : x+y,                                         *)
(*            0,                                                        *)
(*            (1 :> 2) @@ (2 :> 1) @@ (3 :> 3)) = 13                    *)
(*    The third argument represents the bag {| 1, 1, 2, 3, 3, 3 |}.     *)
(************************************************************************)
FoldBag(op(_,_), base, B) ==
   MapThenFoldBag(op, base, LAMBDA x: x, LAMBDA S : CHOOSE x \in S : TRUE, B)

(************************************************************************)
(* Compute the sum of the elements of B.                                *)
(************************************************************************)
SumBag(B) ==
   FoldBag(LAMBDA x,y : x+y, 0, B)

(************************************************************************)
(* Compute the product of the elements of B.                            *)
(************************************************************************)
ProductBag(B) ==
   FoldBag(LAMBDA x,y : x*y, 1, B)

=============================================================================
