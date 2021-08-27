------------------------------- MODULE Folds -------------------------------

MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
(******************************************************************************)
(* Starting from base, apply op to f(x), for all x \in S, by choosing the set *)
(* elements with `choose`. If there are multiple ways for choosing an element,*)
(* op should be associative and commutative. Otherwise, the result may depend *)
(* on the concrete implementation of `choose`.                                *)
(*                                                                            *)
(* FoldSet, a simpler version for sets is contained in FiniteSetsEx.          *)
(* FoldFunction, a simpler version for functions is contained in Functions.   *)
(* FoldSequence, a simpler version for sequences is contained in SequencesExt.*)
(*                                                                            *)
(* Example:                                                                   *)
(*                                                                            *)
(*  MapThenFoldSet(LAMBDA x,y: x \cup y,                                      *)
(*                 {1,2},                                                     *)
(*                 LAMBDA x: {{x}},                                           *)
(*                 LAMBDA set: CHOOSE x \in set: TRUE,                        *)
(*                 S)                                                         *)
(*       = {{1},{2}}                                                          *)
(******************************************************************************)
  \* By comparing S to {}, we help TLC in producing a reasonable error trace
  IF S = {}
  THEN base
  ELSE
    LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
    IN  iter[S]




=============================================================================
\* Modification History
\* Last modified Thu Aug 26 15:11:48 CEST 2021 by igor
\* Last modified Fri Apr 02 13:54:18 CEST 2021 by marty
\* Created Tue Mar 30 19:20:49 CEST 2021 by marty
