------------------------------ MODULE BagsExt ------------------------------
(***************************************************************************)
(* Additional operators on bags (multisets).                               *)
(***************************************************************************)

LOCAL INSTANCE Bags
LOCAL INSTANCE Integers
LOCAL INSTANCE Folds

\* @supportedBy("TLC,Apalache")
BagAdd(B, x) ==
   (************************************************************************)
   (* Add an element x to bag B.                                           *)
   (* Same as B (+) SetToBag({x}).                                         *)
   (************************************************************************)
   IF x \in DOMAIN B
   THEN [e \in DOMAIN B |-> IF e=x THEN B[e]+1 ELSE B[e]]
   ELSE [e \in DOMAIN B \union {x} |-> IF e=x THEN 1 ELSE B[e]]

\* @supportedBy("TLC,Apalache")
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

\* @supportedBy("TLC,Apalache")
BagRemoveAll(B,x) ==
   (************************************************************************)
   (* Remove all copies of an element x from bag B.                        *)
   (************************************************************************)
   [e \in DOMAIN B \ {x} |-> B[e]]
 
\* @supportedBy("TLC")
MapThenFoldBag(op(_,_), base, f(_), choose(_), B) ==
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
    LET handle(x) ==  \* handle all occurrences of x in B
        LET pow[n \in Nat \ {0}] ==
            op(IF n=1 THEN base ELSE pow[n-1], f(x))
        IN  pow[B[x]]
    IN  MapThenFoldSet(op, base, handle,
                       LAMBDA S : CHOOSE x \in S : TRUE,
                       DOMAIN B)

\* @supportedBy("TLC")
FoldBag(op(_,_), base, B) ==
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

\* @supportedBy("TLC,Apalache")
SumBag(B) ==
   (************************************************************************)
   (* Compute the sum of the elements of B.                                *)
   (************************************************************************)
   FoldBag(LAMBDA x,y : x+y, 0, B)

\* @supportedBy("TLC,Apalache")
ProductBag(B) ==
   (************************************************************************)
   (* Compute the product of the elements of B.                            *)
   (************************************************************************)
   FoldBag(LAMBDA x,y : x*y, 1, B)

=============================================================================
