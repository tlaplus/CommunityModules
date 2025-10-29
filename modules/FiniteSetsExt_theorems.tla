---- MODULE FiniteSetsExt_theorems ----
EXTENDS FiniteSetsExt, FiniteSets, Naturals

LEMMA MapThenSumSetEmpty ==
    ASSUME NEW op(_)
    PROVE MapThenSumSet(op, {}) = 0
PROOF OMITTED \* Proof in FiniteSetsExt_theorems_proofs.tla


LEMMA MapThenSumSetType ==
    ASSUME NEW S, IsFiniteSet(S), NEW op(_), \A e \in S : op(e) \in Nat
    PROVE MapThenSumSet(op, S) \in Nat
PROOF OMITTED \* Proof in FiniteSetsExt_theorems_proofs.tla


THEOREM MapThenSumSetAddElem ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e, e \notin S, op(e) \in Nat
    PROVE MapThenSumSet(op, S \cup {e}) = MapThenSumSet(op, S) + op(e)
PROOF OMITTED \* Proof in FiniteSetsExt_theorems_proofs.tla

LEMMA MapThenSumSetRemElem ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e \in S
    PROVE MapThenSumSet(op, S) = MapThenSumSet(op, S \ {e}) + op(e)
PROOF OMITTED \* Proof in FiniteSetsExt_theorems_proofs.tla

LEMMA MapThenSumSetMonotonic ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e, e \notin S, op(e) \in Nat
    PROVE MapThenSumSet(op, S \cup {e}) >= MapThenSumSet(op, S)
PROOF OMITTED \* Proof in FiniteSetsExt_theorems_proofs.tla

LEMMA MapThenSumSetMonotonicOpGE ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op1(_), \A s \in S : op1(s) \in Nat,
        NEW op2(_), \A s \in S : op2(s) \in Nat,
        \A s \in S : op2(s) >= op1(s)
    PROVE
        MapThenSumSet(op2, S) >= MapThenSumSet(op1, S)
PROOF OMITTED \* Proof in FiniteSetsExt_theorems_proofs.tla

LEMMA MapThenSumSetMonotonicOpGT ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op1(_), \A s \in S : op1(s) \in Nat,
        NEW op2(_), \A s \in S : op2(s) \in Nat,
        \A s \in S : op2(s) >= op1(s),
        \E s \in S : op2(s) > op1(s)
    PROVE
        MapThenSumSet(op2, S) > MapThenSumSet(op1, S)
PROOF OMITTED \* Proof in FiniteSetsExt_theorems_proofs.tla

LEMMA MapThenSumSetZero ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A e \in S: op(e) \in Nat,
           MapThenSumSet(op, S) = 0
    PROVE \A e \in S: op(e) = 0
PROOF OMITTED \* Proof in FiniteSetsExt_theorems_proofs.tla

LEMMA MapThenSumSetZeros ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A e \in S: op(e) = 0
    PROVE MapThenSumSet(op, S) = 0
PROOF OMITTED \* Proof in FiniteSetsExt_theorems_proofs.tla

====
