------------------------------ MODULE BagsExt ------------------------------
(***************************************************************************)
(* Additional operators on bags (multisets).                               *)
(***************************************************************************)

LOCAL INSTANCE Bags
LOCAL INSTANCE Naturals
LOCAL INSTANCE Folds

BagAdd(B, x) ==
   (************************************************************************)
   (* Add an element x to bag B.                                           *)
   (************************************************************************)
   IF x \in DOMAIN B
   THEN [e \in DOMAIN B |-> IF e=x THEN B[e]+1 ELSE B[e]]
   ELSE [e \in DOMAIN B \union {x} |-> IF e=x THEN 1 ELSE B[e]]

BagRemove(B,x) ==
   (************************************************************************)
   (* Remove an element x from bag B.                                      *)
   (************************************************************************)
   IF x \in DOMAIN B
   THEN IF B[x] = 1
        THEN [e \in DOMAIN B \ {x} |-> B[e]]
        ELSE [e \in DOMAIN B |-> IF e=x THEN B[e]-1 ELSE B[e]]
   ELSE B

=============================================================================
