------------------------------- MODULE Folds -------------------------------

MapThenFoldSet(op(_,_), base, f(_), ord(_,_), S) ==
(******************************************************************************)
(* Starting from base, apply op to f(x), for all x \in S, in an ordered by    *)
(* ord. If there is no ordering, ord can be always true but then op must be   *)
(* associative and commutative.                                               *)
(*                                                                            *)
(* FoldSet, a simpler version for sets is contained in FiniteSetsEx.          *)
(* FoldFunction, a simpler version for functions is contained in Functions.   *)
(* FoldSequence, a simpler version for sequences is contained in SequencesExt.*)
(*                                                                            *)
(* Example:                                                                   *)
(*                                                                            *)
(*  MapThenFoldSet(LAMBDA x,y: x \cup y,{1,2},LAMBDA x: {{x}}, S) = {{1},{2}} *)
(******************************************************************************)
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == CHOOSE x \in s : \A y \in s \ {x} : ord(x,s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]




=============================================================================
\* Modification History
\* Last modified Wed Mar 31 00:40:51 CEST 2021 by marty
\* Created Tue Mar 30 19:20:49 CEST 2021 by marty
