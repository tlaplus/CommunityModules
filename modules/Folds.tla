------------------------------- MODULE Folds -------------------------------

MapThenFoldSet(op(_,_), base, f(_), S) ==
(******************************************************************************)
(* Starting from base, apply op to f(x), for all x \in S, in an arbitrary     *)
(* order. It is assumed that op is associative and commutative.               *)
(*                                                                            *)
(* FoldSet, a simpler version for sets is contained in FiniteSetsEx.          *)
(* FoldFunction, a simpler version for functions is contained in Functions.   *)
(*                                                                            *)
(* Example:                                                                   *)
(*                                                                            *)
(*  MapThenFoldSet(LAMBDA x,y: x \cup y,{1,2},LAMBDA x: {{x}}, S) = {{1},{2}} *)
(******************************************************************************)
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == CHOOSE x \in s : TRUE
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]




=============================================================================
\* Modification History
\* Last modified Tue Mar 30 20:39:02 CEST 2021 by marty
\* Created Tue Mar 30 19:20:49 CEST 2021 by marty
