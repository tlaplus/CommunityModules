-------------------------- MODULE FiniteSetsExt_theorems ------------------
EXTENDS FiniteSetsExt, FiniteSets, Integers
(*************************************************************************)
(* This module only lists theorem statements for reference. The proofs   *)
(* can be found in module FiniteSetsExt_theorems_proofs.tla.             *)
(*************************************************************************)

THEOREM FoldSetEmpty ==
    ASSUME NEW op(_,_), NEW base
    PROVE  FoldSet(op, base, {}) = base

THEOREM FoldSetNonempty ==
    ASSUME NEW op(_,_), NEW base, NEW S, S # {}, IsFiniteSet(S)
    PROVE  \E x \in S : FoldSet(op, base, S) = op(x, FoldSet(op, base, S \ {x}))

THEOREM FoldSetType ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           \A t,u \in Typ : op(t,u) \in Typ
    PROVE  FoldSet(op, base, S) \in Typ

\* more useful version for an associative-commutative operator op
THEOREM FoldSetAC ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, 
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           NEW x \in S
    PROVE  FoldSet(op, base, S) = op(x, FoldSet(op, base, S \ {x}))

---------------------------------------------------------------------------

THEOREM SumSetNat ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  SumSet(S) \in Nat

THEOREM SumSetInt ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  SumSet(S) \in Int

THEOREM SumSetEmpty == SumSet({}) = 0

THEOREM SumSetNonempty ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S 
    PROVE  SumSet(S) = x + SumSet(S \ {x})

THEOREM SumSetNatZero ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  SumSet(S) = 0 <=> S \subseteq {0}

---------------------------------------------------------------------------

THEOREM ProductSetNat ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  ProductSet(S) \in Nat

THEOREM ProductSetInt ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  ProductSet(S) \in Int

THEOREM ProductSetNonempty ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S 
    PROVE  ProductSet(S) = x * ProductSet(S \ {x})

THEOREM ProductSetNatOne ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  ProductSet(S) = 1 <=> S \subseteq {1}

THEOREM ProductSetZero ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  ProductSet(S) = 0 <=> 0 \in S 

---------------------------------------------------------------------------

THEOREM MapThenSumSetNat ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Nat
    PROVE  MapThenSumSet(op, S) \in Nat

THEOREM MapThenSumSetInt ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Int
    PROVE  MapThenSumSet(op, S) \in Int

THEOREM MapThenSumSetEmpty == 
    ASSUME NEW op(_)
    PROVE  MapThenSumSet(op, {}) = 0

THEOREM MapThenSumSetNonempty ==
    ASSUME NEW S, IsFiniteSet(S), NEW x \in S,
           NEW op(_), \A s \in S : op(s) \in Int
    PROVE  MapThenSumSet(op, S) = op(x) + MapThenSumSet(op, S \ {x})

THEOREM MapThenSumSetZero ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Nat 
    PROVE  MapThenSumSet(op, S) = 0 <=> \A s \in S : op(s) = 0

THEOREM MapThenSumSetMonotonic ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), \A s \in S : f(s) \in Int,
           NEW g(_), \A s \in S : g(s) \in Int,
           \A s \in S : f(s) <= g(s)
    PROVE  MapThenSumSet(f, S) <= MapThenSumSet(g, S)

THEOREM MapThenSumSetStrictlyMonotonic ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), \A s \in S : f(s) \in Int,
           NEW g(_), \A s \in S : g(s) \in Int,
           \A s \in S : f(s) <= g(s),
           \E s \in S : f(s) < g(s)
    PROVE  MapThenSumSet(f, S) < MapThenSumSet(g, S)

===========================================================================
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
