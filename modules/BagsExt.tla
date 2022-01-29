------------------------------ MODULE BagsExt ------------------------------
(***************************************************************************)
(* Additional operators on bags (multisets).                               *)
(***************************************************************************)

LOCAL INSTANCE Bags
LOCAL INSTANCE Integers
LOCAL INSTANCE Folds

BagAdd(B, x) ==
   (************************************************************************)
   (* Add an element x to bag B.                                           *)
   (* Same as B (+) SetToBag({x}).                                         *)
   (************************************************************************)
   IF x \in DOMAIN B
   THEN [e \in DOMAIN B |-> IF e=x THEN B[e]+1 ELSE B[e]]
   ELSE [e \in DOMAIN B \union {x} |-> IF e=x THEN 1 ELSE B[e]]

BagRemove(B,x) ==
   (************************************************************************)
   (* Remove an element x from bag B.                                      *)
   (* Same as B (-) SetToBag({x}).                                         *)
   (************************************************************************)
   IF x \in DOMAIN B
   THEN IF B[x] = 1
        THEN [e \in DOMAIN B \ {x} |-> B[e]]
        ELSE [e \in DOMAIN B |-> IF e=x THEN B[e]-1 ELSE B[e]]
   ELSE B

FoldBag(op(_,_), base, B) ==
   (************************************************************************)
   (* Fold op over all elements of bag B, starting with value base.        *)
   (*                                                                      *)
   (* Example:                                                             *)
   (*    FoldBag(LAMBDA x,y : x+y,                                         *)
   (*            0,                                                        *)
   (*            (1 :> 2) @@ (2 :> 1) @@ (3 :> 2)) = 10                    *)
   (*    The third argument represents the bag {| 1, 1, 2, 3, 3 |}.        *)
   (************************************************************************)
   LET repl(x) ==
         (* replicate operation op for all occurrences of x in B *)
       LET it[n \in Nat \ {0}] ==
           IF n = 1 THEN x ELSE op(x, it[n-1])
       IN  it[B[x]]
   IN  MapThenFoldSet(op, base, repl, 
                      LAMBDA S : CHOOSE x \in S : TRUE,
                      DOMAIN B)

SumBag(B) ==
   (************************************************************************)
   (* Compute the sum of the elements of B.                                *)
   (************************************************************************)
   FoldBag(LAMBDA x,y : x+y, 0, B)

ProductBag(B) ==
   (************************************************************************)
   (* Compute the product of the elements of B.                            *)
   (************************************************************************)
   FoldBag(LAMBDA x,y : x*y, 1, B)

=============================================================================
