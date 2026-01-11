-------------------------- MODULE FiniteSetsExtTheorems -------------------
EXTENDS FiniteSetsExt, FiniteSets, Integers
(*************************************************************************)
(* This module only lists theorem statements for reference. The proofs   *)
(* can be found in module FiniteSetsExtTheorems_proofs.tla.              *)
(*************************************************************************)

(*************************************************************************)
(* Folding over an empty set produces the base value.                    *)
(*************************************************************************)
THEOREM FoldSetEmpty ==
    ASSUME NEW op(_,_), NEW base
    PROVE  FoldSet(op, base, {}) = base

(*************************************************************************)
(* Folding over a finite non-empty set corresponds to applying the       *)
(* underlying binary operator to some element of the set and the result  *)
(* of folding the remaining set elements.                                *)
(*************************************************************************)
THEOREM FoldSetNonempty ==
    ASSUME NEW op(_,_), NEW base, NEW S, S # {}, IsFiniteSet(S)
    PROVE  \E x \in S : FoldSet(op, base, S) = op(x, FoldSet(op, base, S \ {x}))

(*************************************************************************)
(* The type of folding a set corresponds to the type associated with the *)
(* binary operator that underlies the fold.                              *)
(*************************************************************************)
THEOREM FoldSetType ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           \A t,u \in Typ : op(t,u) \in Typ
    PROVE  FoldSet(op, base, S) \in Typ

(*************************************************************************)
(* If the binary operator is associative and commutative, the result of  *)
(* folding over a non-empty set corresponds to applying the operator to  *)
(* an arbitrary element of the set and the result of folding the         *)
(* remainder of the set.                                                 *)
(*************************************************************************)
THEOREM FoldSetAC ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, 
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           NEW x \in S
    PROVE  FoldSet(op, base, S) = op(x, FoldSet(op, base, S \ {x}))

\* reformulation in terms of adding an element to the set
THEOREM FoldSetACAddElement ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, 
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           NEW x \in Typ \ S
    PROVE  FoldSet(op, base, S \union {x}) = op(x, FoldSet(op, base, S))

(*************************************************************************)
(* For an AC operator `op` for which `base` is the neutral element,      *)
(* folding commutes with set union, for disjoint sets.                   *)
(*************************************************************************)
THEOREM FoldSetDisjointUnion ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, 
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           \A t \in Typ : op(base, t) = t,
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           NEW T \in SUBSET Typ, IsFiniteSet(T), S \cap T = {}
    PROVE  FoldSet(op, base, S \union T) = 
           op(FoldSet(op, base, S), FoldSet(op, base, T))

---------------------------------------------------------------------------

(*************************************************************************)
(* The sum of a set of natural numbers, resp. integers is a natural      *)
(* number, resp. an integer.                                             *)
(*************************************************************************)
THEOREM SumSetNat ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  SumSet(S) \in Nat

THEOREM SumSetInt ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  SumSet(S) \in Int

(*************************************************************************)
(* The sum of the empty set is 0.                                        *)
(*************************************************************************)
THEOREM SumSetEmpty == SumSet({}) = 0

(*************************************************************************)
(* The sum of a finite non-empty set is the sum of an arbitrary element  *)
(* and the sum of the remaining elements.                                *)
(*************************************************************************)
THEOREM SumSetNonempty ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S 
    PROVE  SumSet(S) = x + SumSet(S \ {x})

\* reformulation of the above in terms of adding an element to a set
THEOREM SumSetAddElement ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in Int \ S
    PROVE  SumSet(S \union {x}) = x + SumSet(S)

(*************************************************************************)
(* Set summation distributes over union, for disjoint sets of integers.  *)
(*************************************************************************)
THEOREM SumSetDisjointUnion ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S),
           NEW T \in SUBSET Int, IsFiniteSet(T), S \cap T = {}
    PROVE  SumSet(S \union T) = SumSet(S) + SumSet(T)

(*************************************************************************)
(* The sum of a subset of a set of natural numbers is bounded by the sum *)
(* of the full set.                                                      *)
(*************************************************************************)
THEOREM SumSetNatSubset ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S),
           NEW T \in SUBSET S
    PROVE  SumSet(T) <= SumSet(S)

(*************************************************************************)
(* The sum of a set of natural numbers is zero only if the set is empty  *)
(* or the singleton {0}.                                                 *)
(*************************************************************************)
THEOREM SumSetNatZero ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  SumSet(S) = 0 <=> S \subseteq {0}

---------------------------------------------------------------------------

(*************************************************************************)
(* The product of a set of natural numbers, resp. integers is a natural  *)
(* number, resp. an integer.                                             *)
(*************************************************************************)
THEOREM ProductSetNat ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  ProductSet(S) \in Nat

THEOREM ProductSetInt ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  ProductSet(S) \in Int

(*************************************************************************)
(* The product of the empty set is 1.                                    *)
(*************************************************************************)
THEOREM ProductSetEmpty == ProductSet({}) = 1

(*************************************************************************)
(* The product of a finite non-empty set is the product of an arbitrary  *)
(* element and the product of the remaining elements.                    *)
(*************************************************************************)
THEOREM ProductSetNonempty ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S 
    PROVE  ProductSet(S) = x * ProductSet(S \ {x})

\* reformulation of the above in terms of adding an element to the set
THEOREM ProductSetAddElement ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in Int \ S
    PROVE  ProductSet(S \union {x}) = x * ProductSet(S)

(*************************************************************************)
(* Set product distributes over union, for disjoint sets of integers.    *)
(*************************************************************************)
THEOREM ProductSetDisjointUnion ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S),
           NEW T \in SUBSET Int, IsFiniteSet(T), S \cap T = {}
    PROVE  ProductSet(S \union T) = ProductSet(S) * ProductSet(T)

(*************************************************************************)
(* The product of a set of natural numbers is one only if the set is     *)
(* empty or the singleton {1}.                                           *)
(*************************************************************************)
THEOREM ProductSetNatOne ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  ProductSet(S) = 1 <=> S \subseteq {1}

(*************************************************************************)
(* The product of a set of integers is zero only if the set contains 0.  *)
(*************************************************************************)
THEOREM ProductSetZero ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  ProductSet(S) = 0 <=> 0 \in S 

(*************************************************************************)
(* The product of a subset of a set of non-zero natural numbers is       *)
(* bounded by the product of the full set.                               *)
(*************************************************************************)
THEOREM ProductSetNatSubset ==
    ASSUME NEW S \in SUBSET Nat \ {0}, IsFiniteSet(S),
           NEW T \in SUBSET S
    PROVE  ProductSet(T) <= ProductSet(S)

---------------------------------------------------------------------------

(*************************************************************************)
(* For an operator that maps set elements to natural numbers, resp.      *)
(* integers, MapThenSumSet yields a natural number, resp. an integer.    *)
(*************************************************************************)
THEOREM MapThenSumSetNat ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Nat
    PROVE  MapThenSumSet(op, S) \in Nat

THEOREM MapThenSumSetInt ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Int
    PROVE  MapThenSumSet(op, S) \in Int

(*************************************************************************)
(* The sum of mapping the empty set is 0.                                *)
(*************************************************************************)
THEOREM MapThenSumSetEmpty == 
    ASSUME NEW op(_)
    PROVE  MapThenSumSet(op, {}) = 0

(*************************************************************************)
(* The sum of mapping a finite non-empty set is the sum of the image of  *)
(* an arbitrary element and the sum of mapping the remaining elements.   *)
(*************************************************************************)
THEOREM MapThenSumSetNonempty ==
    ASSUME NEW S, IsFiniteSet(S), NEW x \in S,
           NEW op(_), \A s \in S : op(s) \in Int
    PROVE  MapThenSumSet(op, S) = op(x) + MapThenSumSet(op, S \ {x})

\* reformulation of the above in terms of adding an element to the set
THEOREM MapThenSumSetAddElement ==
    ASSUME NEW S, IsFiniteSet(S), NEW x, x \notin S,
           NEW op(_), \A s \in S \union {x} : op(s) \in Int
    PROVE  MapThenSumSet(op, S \union {x}) = op(x) + MapThenSumSet(op, S)

(*************************************************************************)
(* Mapping then summing distributes over union, for disjoint finite sets *)
(* of integers.                                                          *)
(*************************************************************************)
THEOREM MapThenSumSetDisjointUnion ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW T, IsFiniteSet(T), S \cap T = {},
           NEW op(_), \A x \in S \union T : op(x) \in Int
    PROVE  MapThenSumSet(op, S \union T) = 
           MapThenSumSet(op, S) + MapThenSumSet(op, T)

(*************************************************************************)
(* The map-sum of a subset of a finite set of natural numbers is bounded *)
(* by the product of the full set.                                       *)
(*************************************************************************)
THEOREM MapThenSumSetNatSubset ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW T \in SUBSET S,
           NEW op(_), \A x \in S : op(x) \in Nat
    PROVE  MapThenSumSet(op, T) <= MapThenSumSet(op, S)

(*************************************************************************)
(* The map-sum of a finite set of natural numbers is zero only if all    *)
(* set elements are mapped to zero.                                      *)
(*************************************************************************)
THEOREM MapThenSumSetZero ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Nat 
    PROVE  MapThenSumSet(op, S) = 0 <=> \A s \in S : op(s) = 0

(*************************************************************************)
(* The map-sum of a finite set of natural numbers is monotonic in the    *)
(* function argument                                                     *)
(*************************************************************************)
THEOREM MapThenSumSetMonotonic ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), \A s \in S : f(s) \in Int,
           NEW g(_), \A s \in S : g(s) \in Int,
           \A s \in S : f(s) <= g(s)
    PROVE  MapThenSumSet(f, S) <= MapThenSumSet(g, S)

(*************************************************************************)
(* Moreover, if the second function returns a larger value for at least  *)
(* one element of the set, then the map-sum will be strictly larger.     *)
(*************************************************************************)
THEOREM MapThenSumSetStrictlyMonotonic ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), \A s \in S : f(s) \in Int,
           NEW g(_), \A s \in S : g(s) \in Int,
           \A s \in S : f(s) <= g(s),
           NEW s \in S, f(s) < g(s)
    PROVE  MapThenSumSet(f, S) < MapThenSumSet(g, S)

---------------------------------------------------------------------------

(*************************************************************************)
(* Theorems about Min and Max of sets of integers.                       *)
(*************************************************************************)

(*************************************************************************)
(* If a set of integers contains an upper bound, it is the maximum.      *)
(*************************************************************************)
THEOREM MaxInt ==
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x >= y
    PROVE  Max(S) = x

(*************************************************************************)
(* Any finite non-empty set of integers has a maximum.                   *)
(*************************************************************************)
THEOREM MaxIntFinite ==
    ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
    PROVE  /\ Max(S) \in S
           /\ \A y \in S : Max(S) >= y

(*************************************************************************)
(* Any non-empty set of integers that has an upper bound has a maximum.  *)
(*************************************************************************)
THEOREM MaxIntBounded ==
    ASSUME NEW S \in SUBSET Int, S # {}, NEW x \in Int, \A y \in S : x >= y
    PROVE  /\ Max(S) \in S 
           /\ \A y \in S : Max(S) >= y

(*************************************************************************)
(* The maximum of a non-empty interval is its upper bound.               *)
(*************************************************************************)
THEOREM MaxInterval ==
    ASSUME NEW a \in Int, NEW b \in Int, a <= b 
    PROVE  Max(a..b) = b

(*************************************************************************)
(* If a set of integers contains an lower bound, it is the minimum.      *)
(*************************************************************************)
THEOREM MinInt ==
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x <= y
    PROVE  Min(S) = x

(*************************************************************************)
(* Any finite non-empty set of integers has a minimum.                   *)
(*************************************************************************)
THEOREM MinIntFinite ==
    ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
    PROVE  /\ Min(S) \in S
           /\ \A y \in S : Min(S) <= y

(*************************************************************************)
(* Any non-empty set of integers that has a lower bound has a minimum.   *)
(*************************************************************************)
THEOREM MinIntBounded ==
    ASSUME NEW S \in SUBSET Int, S # {}, NEW x \in Int, \A y \in S : x <= y
    PROVE  /\ Min(S) \in S 
           /\ \A y \in S : Min(S) <= y

(*************************************************************************)
(* The minimum of a non-empty interval is its lower bound.               *)
(*************************************************************************)
THEOREM MinInterval ==
    ASSUME NEW a \in Int, NEW b \in Int, a <= b 
    PROVE  Min(a..b) = a

(*************************************************************************)
(* Any non-empty set of natural numbers has a minimum.                   *)
(*************************************************************************)
THEOREM MinNat ==
    ASSUME NEW S \in SUBSET Nat, S # {}
    PROVE  /\ Min(S) \in S 
           /\ \A y \in S : Min(S) <= y


===========================================================================
