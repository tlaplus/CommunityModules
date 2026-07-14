----------------------------- MODULE QuorumTheorems -------------------------
EXTENDS Quorum, Integers, FiniteSets

(***************************************************************************)
(* Direct consequences of the definition of a quorum system.               *)
(***************************************************************************)

THEOREM QuorumsIntersect ==
    ASSUME NEW S, NEW QS \in QuorumSystem(S), NEW Q1 \in QS, NEW Q2 \in QS 
    PROVE  \E s \in S : s \in Q1 \cap Q2 

THEOREM QuorumSuperset ==
    ASSUME NEW S, NEW QS \in QuorumSystem(S), 
           NEW Q1 \in QS, NEW Q2 \in SUBSET S, Q1 \subseteq Q2
    PROVE  Q2 \in QS 

(***************************************************************************)
(* Strict majorities of a non-empty set S form a quorum system.            *)
(***************************************************************************)

THEOREM MajoritiesQuorumSystem ==
    ASSUME NEW S, IsFiniteSet(S), S # {}
    PROVE  { Q \in SUBSET S : 2 * Cardinality(Q) > Cardinality(S) }
           \in QuorumSystem(S)

=============================================================================
