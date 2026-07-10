--------------------------------- MODULE Quorum -----------------------------

(***************************************************************************)
(* A quorum system for a set S is a non-empty collection of quorums, i.e.  *)
(* subsets of S such that any two quorums intersect. It is typically also  *)
(* assumed that a superset of a quorum is itself a quorum.                 *)
(*                                                                         *)
(* For example, given a finite and non-empty set S of servers, the sets of *)
(* strict majorities among servers form a quorum system.                   *)
(***************************************************************************)

QuorumSystem(S) ==
    { QS \in SUBSET (SUBSET S) :
         /\ QS # {}
         /\ \A Q1, Q2 \in QS : Q1 \cap Q2 # {}
         /\ \A Q1, Q2 \in SUBSET S : Q1 \in QS /\ Q1 \subseteq Q2 => Q2 \in QS
    }

=============================================================================
