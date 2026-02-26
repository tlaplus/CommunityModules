----------------------------- MODULE Relation ------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

(***************************************************************************)
(* This module provides some basic operations on relations, represented    *)
(* as binary Boolean functions over some set S.                            *)
(*                                                                         *)
(* Relations are represented as functions R: S × S → BOOLEAN, where        *)
(* R[x,y] = TRUE means that x is related to y.                             *)
(*                                                                         *)
(* The module includes:                                                    *)
(*   - Basic relation properties (reflexive, symmetric, transitive, etc.)  *)
(*   - Ordering relations (partial orders, total orders)                   *)
(*   - Closure operations (transitive closure)                             *)
(*   - Connectivity analysis                                               *)
(*                                                                         *)
(* Each property has two variants:                                         *)
(*   - Direct: Takes a relation R as a Boolean function                    *)
(*   - Under: Takes a binary operator and constructs the relation          *)
(***************************************************************************)

(***************************************************************************)
(* Is the relation R reflexive over S?                                     *)
(*                                                                         *)
(* A relation is reflexive if every element is related to itself.          *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsReflexive([<<x,y>> \in {1,2}×{1,2} |-> x=y], {1,2}) = TRUE          *)
(*   IsReflexiveUnder(=, {1,2,3}) = TRUE                                   *)
(*   IsReflexiveUnder(<, {1,2,3}) = FALSE                                  *)
(***************************************************************************)
IsReflexive(R, S) == \A x \in S : R[x,x]

IsReflexiveUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsReflexive([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsReflexive([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Is the relation R irreflexive over set S?                               *)
(*                                                                         *)
(* A relation is irreflexive if no element is related to itself.           *)
(* This is the opposite of reflexive.                                      *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsIrreflexiveUnder(<, {1,2,3}) = TRUE                                 *)
(*   IsIrreflexiveUnder(<=, {1,2,3}) = FALSE                               *)
(***************************************************************************)
IsIrreflexive(R, S) == \A x \in S : ~ R[x,x]

IsIrreflexiveUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsIrreflexive([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsIrreflexive([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Is the relation R symmetric over set S?                                 *)
(*                                                                         *)
(* A relation is symmetric if x related to y implies y related to x.       *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsSymmetricUnder(=, {1,2,3}) = TRUE                                   *)
(*   IsSymmetricUnder(<, {1,2,3}) = FALSE                                  *)
(***************************************************************************)
IsSymmetric(R, S) == \A x,y \in S : R[x,y] <=> R[y,x]

IsSymmetricUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsSymmetric([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsSymmetric([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Is the relation R antisymmetric over set S?                             *)
(*                                                                         *)
(* A relation is antisymmetric if x related to y and y related to x        *)
(* implies x equals y.                                                     *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsAntiSymmetricUnder(<=, {1,2,3}) = TRUE                              *)
(*   IsAntiSymmetricUnder(=, {1,2,3}) = TRUE                               *)
(***************************************************************************)
IsAntiSymmetric(R, S) == \A x,y \in S : R[x,y] /\ R[y,x] => x=y

IsAntiSymmetricUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsAntiSymmetric([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsAntiSymmetric([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Is the relation R asymmetric over set S?                                *)
(*                                                                         *)
(* A relation is asymmetric if it's never the case that both x is related  *)
(* to y and y is related to x (unless x=y).                                *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsAsymmetricUnder(<, {1,2,3}) = TRUE                                  *)
(*   IsAsymmetricUnder(<=, {1,2,3}) = FALSE (due to reflexivity)           *)
(***************************************************************************)
IsAsymmetric(R, S) == \A x,y \in S : ~(R[x,y] /\ R[y,x])

IsAsymmetricUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsAsymmetric([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsAsymmetric([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Is the relation R transitive over set S?                                *)
(*                                                                         *)
(* A relation is transitive if x related to y and y related to z implies   *)
(* x related to z.                                                         *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsTransitiveUnder(<, {1,2,3}) = TRUE                                  *)
(*   IsTransitiveUnder(=, {1,2,3}) = TRUE                                  *)
(***************************************************************************)
IsTransitive(R, S) == \A x,y,z \in S : R[x,y] /\ R[y,z] => R[x,z]

IsTransitiveUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsTransitive([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsTransitive([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Is the set S strictly partially ordered under the (binary) relation R?  *)
(*                                                                         *)
(* A strict partial order combines irreflexivity, antisymmetry, and        *)
(* transitivity.                                                           *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsStrictlyPartiallyOrderedUnder(<, {1,2,3}) = TRUE                    *)
(*   IsStrictlyPartiallyOrderedUnder(<=, {1,2,3}) = FALSE (not irreflexive)*)
(***************************************************************************)
IsStrictlyPartiallyOrdered(R, S) ==
    /\ IsIrreflexive(R, S)
    /\ IsAntiSymmetric(R, S)
    /\ IsTransitive(R, S)

IsStrictlyPartiallyOrderedUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsStrictlyPartiallyOrdered([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsStrictlyPartiallyOrdered([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Is the set S (weakly) partially ordered under the (binary) relation R?  *)
(*                                                                         *)
(* A partial order (poset) combines reflexivity, antisymmetry, and         *)
(* transitivity.                                                           *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsPartiallyOrderedUnder(<=, {1,2,3}) = TRUE                           *)
(*   IsPartiallyOrderedUnder(<, {1,2,3}) = FALSE (not reflexive)           *)
(***************************************************************************)
IsPartiallyOrdered(R, S) ==
    /\ IsReflexive(R, S)
    /\ IsAntiSymmetric(R, S)
    /\ IsTransitive(R, S)

IsPartiallyOrderedUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsPartiallyOrdered([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsPartiallyOrdered([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Is the set S strictly totally ordered under the (binary) relation R?    *)
(*                                                                         *)
(* A strict total order is a strict partial order where any two distinct   *)
(* elements are comparable (trichotomy property).                          *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsStrictlyTotallyOrderedUnder(<, {1,2,3}) = TRUE                      *)
(***************************************************************************)
IsStrictlyTotallyOrdered(R, S) ==
    /\ IsStrictlyPartiallyOrdered(R, S)
    \* Trichotomy (R is irreflexive)
    /\ \A x,y \in S : x # y => R[x,y] \/ R[y,x]

IsStrictlyTotallyOrderedUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsStrictlyTotallyOrdered([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsStrictlyTotallyOrdered([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Is the set S totally ordered under the (binary) relation R?             *)
(*                                                                         *)
(* A total order is a partial order where any two elements are comparable. *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsTotallyOrderedUnder(<=, {1,2,3}) = TRUE                             *)
(***************************************************************************)
IsTotallyOrdered(R, S) ==
    /\ IsPartiallyOrdered(R, S)
    /\ \A x,y \in S : R[x,y] \/ R[y,x]

IsTotallyOrderedUnder(op(_,_), S) ==
\* revert to the following syntax once TLAPS uses SANY
\* (https://github.com/tlaplus/tlapm/issues/213)
\*    IsTotallyOrdered([<<x,y>> \in S \X S |-> op(x,y)], S)
    IsTotallyOrdered([p \in S \X S |-> op(p[1], p[2])], S)

(***************************************************************************)
(* Compute the transitive closure of relation R over set S.                *)
(***************************************************************************)
TransitiveClosure(R, S) ==
  LET N == Cardinality(S)
      trcl[n \in Nat] == 
          [x,y \in S |-> IF n=0 THEN R[x,y]
                         ELSE \/ trcl[n-1][x,y]
                              \/ \E z \in S : trcl[n-1][x,z] /\ trcl[n-1][z,y]]
  IN  trcl[N]

(***************************************************************************)
(* Compute the reflexive transitive closure of relation R over set S.      *)
(***************************************************************************)
ReflexiveTransitiveClosure(R, S) ==
  LET trcl == TransitiveClosure(R,S)
  IN  [x,y \in S |-> x=y \/ trcl[x,y]]

(***************************************************************************)
(* Is the relation R connected over set S, i.e. does there exist a path    *)
(* between two arbitrary elements of S?                                    *)
(***************************************************************************)
IsConnected(R, S) ==
  LET rtrcl == ReflexiveTransitiveClosure(R,S)
  IN  \A x,y \in S : rtrcl[x,y]

=============================================================================
