------------------------ MODULE FunctionTheorems ----------------------------
(***************************************************************************)
(* `^{\large \vspace{12pt}                                                 *)
(*  Proofs of facts about functions.                                       *)
(*  Originally contributed by Tom Rodeheffer, MSR.                         *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

EXTENDS Functions, Integers, FiniteSets

(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Function restriction.                                                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_RestrictProperties ==
  ASSUME NEW S, NEW T, NEW f \in [S -> T], NEW A \in SUBSET S
  PROVE  /\ Restrict(f,A) \in [A -> T]
         /\ \A x \in A : Restrict(f,A)[x] = f[x]

(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Range of a function.                                                    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_RangeProperties ==
  ASSUME NEW S, NEW T, NEW f \in [S -> T]
  PROVE  /\ Range(f) \subseteq T
         /\ \A y \in Range(f) : \E x \in S : f[x] = y
         /\ f \in Surjection(S, Range(f))


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Inverse of a function.                                                  *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_InverseProperties ==
  ASSUME NEW S, NEW T, NEW f \in [S -> T]
  PROVE  /\ (S = {} => T = {}) => Inverse(f,S,T) \in [T -> S]
         /\ \A y \in Range(f) : f[Inverse(f,S,T)[y]] = y


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Introduction rules for injections, surjections, bijections.             *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_IsInj ==
  ASSUME NEW S, NEW T, NEW F \in [S -> T],
         \A a,b \in S : F[a] = F[b] => a = b
  PROVE  F \in Injection(S,T)

THEOREM Fun_IsSurj ==
  ASSUME NEW S, NEW T, NEW F \in [S -> T],
         \A t \in T : \E s \in S : F[s] = t
  PROVE  F \in Surjection(S,T)

THEOREM Fun_IsBij ==
  ASSUME NEW S, NEW T, NEW F,
         \/ F \in Injection(S,T)
         \/ (F \in [S -> T] /\ \A a,b \in S : F[a] = F[b] => a = b),

         \/ F \in Surjection(S,T)
         \/ (F \in [S -> T] /\ \A t \in T : \E s \in S : F[s] = t)
  PROVE  F \in Bijection(S,T)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Properties of injections, surjections, and bijections.                  *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_InjectionProperties ==
  ASSUME NEW S, NEW T, NEW F \in Injection(S,T)
  PROVE  /\ F \in [S -> T]
         /\ \A a,b \in S : F[a] = F[b] => a = b

THEOREM Fun_SurjectionProperties ==
  ASSUME NEW S, NEW T, NEW F \in Surjection(S,T)
  PROVE  /\ F \in [S -> T]
         /\ \A t \in T : \E s \in S : F[s] = t
         /\ Range(F) = T

THEOREM Fun_BijectionProperties ==
  ASSUME NEW S, NEW T, NEW F \in Bijection(S,T)
  PROVE  /\ F \in [S -> T]
         /\ F \in Injection(S,T)
         /\ F \in Surjection(S,T)
         /\ \A a,b \in S : F[a] = F[b] => a = b
         /\ \A t \in T : \E s \in S : F[s] = t


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* A surjection in [S -> T] such that there is no surjection from any      *)
(* subset of S to T is a bijection.                                        *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_SmallestSurjectionIsBijection ==
  ASSUME NEW S, NEW T, NEW f \in Surjection(S,T),
         \A U \in SUBSET S : U # S => Surjection(U,T) = {}
  PROVE  f \in Bijection(S,T)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Transitivity of injections, surjections, bijections.                    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_InjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Injection(S,T),
         NEW G \in Injection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Injection(S,U)

THEOREM Fun_SurjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Surjection(S,T),
         NEW G \in Surjection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Surjection(S,U)

THEOREM Fun_BijTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Bijection(S,T),
         NEW G \in Bijection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Bijection(S,U)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The inverse of a surjection is an injection and vice versa.             *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_SurjInverse ==
  ASSUME NEW S, NEW T, NEW f \in Surjection(S,T)
  PROVE  Inverse(f,S,T) \in Injection(T,S)

THEOREM Fun_InjInverse ==
  ASSUME NEW S, NEW T, NEW f \in Injection(S,T), S = {} => T = {}
  PROVE  Inverse(f,S,T) \in Surjection(T,S)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Properties of the inverse of a bijection.                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_BijInverse ==
  ASSUME NEW S, NEW T, NEW f \in Bijection(S,T)
  PROVE  /\ Inverse(f,S,T) \in Bijection(T,S)
         /\ \A s \in S : Inverse(f,S,T)[f[s]] = s
         /\ Inverse(Inverse(f,S,T), T,S) = f

(***************************************************************************)
(* We cannot conclude that a function f is a bijection if its inverse is   *)
(* a bijection, and the following is a counter-example.                    *)
(*                                                                         *)
(*   S = {1,2} T = {3,4}                                                   *)
(*   f = [x \in S |-> 3]                                                   *)
(*                                                                         *)
(* Then, Inverse(f,S,T) can very well be (3 :> 1) @@ (4 :> 2), which is a  *)
(* bijection although f is not.                                            *)
(***************************************************************************)

(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The restriction of a bijection is a bijection.                          *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_BijRestrict ==
  ASSUME NEW S, NEW T, NEW F \in Bijection(S,T),
         NEW R \in SUBSET S
  PROVE  Restrict(F, R) \in Bijection(R, Range(Restrict(F, R)))


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Given F an injection from S to T, then F is a bijection from S to F(S). *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_InjMeansBijImage ==
  ASSUME NEW S, NEW T, NEW F \in Injection(S,T)
  PROVE  F \in Bijection(S, Range(F))


-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large \vspace{12pt}                                                 *)
(*  Facts about exists jections.                                           *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Definitions restated as facts.                                          *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsInj ==
  \A S,T : ExistsInjection(S,T)  <=>  Injection(S,T) # {}

THEOREM Fun_ExistsSurj ==
  \A S,T : ExistsSurjection(S,T)  <=>  Surjection(S,T) # {}

THEOREM Fun_ExistsBij ==
  \A S,T : ExistsBijection(S,T)  <=>  Bijection(S,T) # {}


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* There is a surjection from any set S to any non-empty subset T of S.    *)
(* (Note that there cannot be a surjection to {} except if S is empty.)    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsSurjSubset ==
  ASSUME NEW S, NEW T \in SUBSET S, T # {}
  PROVE  ExistsSurjection(S,T)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there is a surjection from S to T, then there is an injection from T *)
(* to S.                                                                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsSurjMeansExistsRevInj ==
  ASSUME NEW S, NEW T, ExistsSurjection(S,T)
  PROVE  ExistsInjection(T,S)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* ExistsBijection is reflexive, symmetric, and transitive.                *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsBijReflexive ==
  ASSUME NEW S
  PROVE  ExistsBijection(S,S)

THEOREM Fun_ExistsBijSymmetric ==
  ASSUME NEW S, NEW T, ExistsBijection(S,T)
  PROVE  ExistsBijection(T,S)

THEOREM Fun_ExistsBijTransitive ==
  ASSUME NEW S, NEW T, NEW U, ExistsBijection(S,T), ExistsBijection(T,U)
  PROVE  ExistsBijection(S,U)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Existence of injections and surjections is reflexive and transitive.    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsInjReflexive ==
  ASSUME NEW S
  PROVE  ExistsInjection(S,S)

THEOREM Fun_ExistsSurjReflexive ==
  ASSUME NEW S
  PROVE  ExistsSurjection(S,S)

THEOREM Fun_ExistsInjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         ExistsInjection(S,T), ExistsInjection(T,U)
  PROVE  ExistsInjection(S,U)

THEOREM Fun_ExistsSurjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         ExistsSurjection(S,T), ExistsSurjection(T,U)
  PROVE  ExistsSurjection(S,U)


-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large \vspace{12pt}                                                 *)
(* The Cantor-Bernstein-Schroeder theorem.                                 *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists an injection from S to T, where T is a subset of S,     *)
(* then there exists a bijection from S to T.                              *)
(*                                                                         *)
(* A lemma for the Cantor-Bernstein-Schroeder theorem.                     *)
(*                                                                         *)
(* This proof is formalized from                                           *)
(* `^\url{http://www.proofwiki.org/wiki/Cantor-Bernstein-Schroeder\_Theorem/Lemma}^' *)
(* retrieved April 29, 2013.                                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_CantorBernsteinSchroeder_Lemma ==
  ASSUME NEW S, NEW T, T \subseteq S, ExistsInjection(S,T)
  PROVE  ExistsBijection(S,T)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If an injection exists from S to T and an injection exists from T to S, *)
(* then there is a bijection from S to T.                                  *)
(*                                                                         *)
(* This is the Cantor-Bernstein-Schroeder theorem.                         *)
(*                                                                         *)
(* This proof is formalized from                                           *)
(* `^\url{http://www.proofwiki.org/wiki/Cantor-Bernstein-Schroeder_Theorem/Proof_5}^' *)
(* retrieved April 29, 2013.                                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_CantorBernsteinSchroeder ==
  ASSUME NEW S, NEW T,
         ExistsInjection(S,T), ExistsInjection(T,S)
  PROVE  ExistsBijection(S,T)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Applications of the Cantor-Bernstein-Schroeder Theorem.                 *)
(* If there exists an injection f: A->B and a surjection g: A->B, then     *)
(* there exists a bijection between A and B.                               *)
(* Also, if there are surjections between A and B, then there is a         *)
(* bijection.                                                              *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

THEOREM Fun_ExistInjAndSurjThenBij ==
  ASSUME NEW S, NEW T,
         ExistsInjection(S,T), ExistsSurjection(S,T)
  PROVE  ExistsBijection(S,T)

THEOREM Fun_ExistSurjAndSurjThenBij ==
  ASSUME NEW S, NEW T,
         ExistsSurjection(S,T), ExistsSurjection(T,S)
  PROVE  ExistsBijection(S,T)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Equivalences for ExistsBijection.                                       *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsBijEquiv ==
  ASSUME NEW S, NEW T
  PROVE  /\ ExistsBijection(S,T) <=> ExistsBijection(T,S)
         /\ ExistsBijection(S,T) <=> ExistsInjection(S,T) /\ ExistsInjection(T,S)
         /\ ExistsBijection(S,T) <=> ExistsInjection(S,T) /\ ExistsSurjection(S,T)
         /\ ExistsBijection(S,T) <=> ExistsInjection(T,S) /\ ExistsSurjection(T,S)
         /\ ExistsBijection(S,T) <=> ExistsSurjection(S,T) /\ ExistsSurjection(T,S)


-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large \vspace{12pt}                                                 *)
(*  Facts about jections involving 1..n.                                   *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* There is a bijection from 1..b-a+1 to a..b for integers a,b with a <= b.*)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsBijInterval ==
  ASSUME NEW a \in Int, NEW b \in Int, a <= b
  PROVE  ExistsBijection(1 .. b-a+1, a .. b)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* There is an injection from 1..n to 1..m iff n \leq m.                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatInjLeq ==
  ASSUME NEW n \in Nat, NEW m \in Nat
  PROVE  ExistsInjection(1..n,1..m) <=> n \leq m


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If a surjection from 1..n to S exists (for some n \in Nat) then a       *)
(* bijection from 1..m to S exists (for some m \in Nat) and m \leq n.      *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatSurjImpliesNatBij ==
  ASSUME NEW S, NEW n \in Nat, ExistsSurjection(1..n,S)
  PROVE  \E m \in Nat : ExistsBijection(1..m,S) /\ m \leq n


(***************************************************************************)
(* Simple corollary.                                                       *)
(***************************************************************************)
THEOREM Fun_NatSurjEquivNatBij ==
  ASSUME NEW S
  PROVE  (\E n \in Nat : ExistsSurjection(1..n,S))
    <=>  (\E m \in Nat : ExistsBijection(1..m,S))


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* For any set S, given n, m \in Nat such that bijections exist from 1..n  *)
(* to S and from 1..m to S, then it must be the case that n = m.           *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijSame ==
  ASSUME NEW S,
         NEW n \in Nat, ExistsBijection(1..n,S),
         NEW m \in Nat, ExistsBijection(1..m,S)
  PROVE  n = m


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* S is empty iff there exists a bijection from 1..0 to S.                 *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijEmpty ==
  ASSUME NEW S
  PROVE  ExistsBijection(1..0,S) <=> S = {}


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* S is a singleton iff there exists a bijection from 1..1 to S.           *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijSingleton ==
  ASSUME NEW S
  PROVE  ExistsBijection(1..1,S) <=> \E s : S = {s}


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists a bijection from 1..m to S (for some m \in Nat), then   *)
(* there exists a bijection from 1..n to T (for some n \in Nat), where T   *)
(* is a subset of S.  Furthermore n \leq m.                                *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijSubset ==
  ASSUME NEW S, NEW m \in Nat, ExistsBijection(1..m,S),
         NEW T \in SUBSET S
  PROVE  \E n \in Nat : ExistsBijection(1..n,T) /\ n \leq m


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists a bijection from 1..m to S (for some m \in Nat), then   *)
(* there exists a bijection from 1..(m+1) to S \cup {x}, where x \notin S. *)
(*                                                                         *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijAddElem ==
  ASSUME NEW S, NEW m \in Nat, ExistsBijection(1..m,S),
         NEW x, x \notin S
  PROVE  ExistsBijection(1..(m+1), S \cup {x})


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists a bijection from 1..m to S (for some m \in Nat), then   *)
(* there exists a bijection from 1..(m-1) to S \ {x}, where x \in S.       *)
(*                                                                         *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijSubElem ==
  ASSUME NEW S, NEW m \in Nat, ExistsBijection(1..m,S),
         NEW x, x \in S
  PROVE  ExistsBijection(1..(m-1), S \ {x})

-----------------------------------------------------------------------------

(***************************************************************************)
(* Folding a function for an empty set of indices yields the base value.   *)
(***************************************************************************)
THEOREM FoldFunctionOnSetEmpty ==
  ASSUME NEW op(_,_), NEW base, NEW fun
  PROVE  FoldFunctionOnSet(op, base, fun, {}) = base 

(***************************************************************************)
(* Folding a function for a non-empty set of indices corresponds to        *)
(* applying the binary operator to f[i], for some i \in indices, and the   *)
(* result of recursing for the set indices \ {i}.                          *)
(***************************************************************************)
THEOREM FoldFunctionOnSetNonempty ==
  ASSUME NEW op(_,_), NEW base, NEW fun, 
         NEW indices, indices # {}, IsFiniteSet(indices)
  PROVE  \E i \in indices : FoldFunctionOnSet(op, base, fun, indices) = 
            op(fun[i], FoldFunctionOnSet(op, base, fun, indices \ {i}))

(***************************************************************************)
(* The type of folding a function corresponds to the type associated with  *)
(* the binary operator that underlies the fold.                            *)
(***************************************************************************)
THEOREM FoldFunctionOnSetType ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         NEW indices, IsFiniteSet(indices), NEW fun,
         \A i \in indices : fun[i] \in Typ
  PROVE FoldFunctionOnSet(op, base, fun, indices) \in Typ

(***************************************************************************)
(* Folding two functions that agree on every element of the set of indices *)
(* yields the same value.                                                  *)
(***************************************************************************)
THEOREM FoldFunctionOnSetEqual ==
  ASSUME NEW op(_,_), NEW base, NEW f, NEW g,
         NEW indices, IsFiniteSet(indices),
         \A i \in indices : f[i] = g[i]
  PROVE  FoldFunctionOnSet(op, base, f, indices) = 
         FoldFunctionOnSet(op, base, g, indices)

(***************************************************************************)
(* If the binary operator is associative and commutative, the result of    *)
(* folding a function over a non-empty set corresponds to applying the     *)
(* operator to an arbitrary element of the set and the result of folding   *)
(* the function over the remainder of the set.                             *)
(***************************************************************************)
THEOREM FoldFunctionOnSetAC ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         \A t,u \in Typ : op(t,u) = op(u,t),
         \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
         NEW indices, IsFiniteSet(indices), NEW i \in indices, NEW fun,
         \A j \in indices : fun[j] \in Typ
  PROVE FoldFunctionOnSet(op, base, fun, indices) =
        op(fun[i], FoldFunctionOnSet(op, base, fun, indices \ {i}))

\* reformulation in terms of adding an index to the set
THEOREM FoldFunctionOnSetACAddIndex ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         \A t,u \in Typ : op(t,u) = op(u,t),
         \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
         NEW indices, IsFiniteSet(indices), NEW i, i \notin indices,
         NEW fun, \A j \in indices \union {i} : fun[j] \in Typ
  PROVE FoldFunctionOnSet(op, base, fun, indices \union {i}) =
        op(fun[i], FoldFunctionOnSet(op, base, fun, indices))

(*************************************************************************)
(* For an AC operator, folding an EXCEPT construction can be reduced to  *)
(* folding the original function.                                        *)
(*************************************************************************)
THEOREM FoldFunctionOnSetACExcept ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         \A t,u \in Typ : op(t,u) = op(u,t),
         \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
         NEW fun, NEW i, NEW y \in Typ,
         NEW indices \in SUBSET (DOMAIN fun), IsFiniteSet(indices), 
         \A j \in indices : fun[j] \in Typ 
  PROVE  FoldFunctionOnSet(op, base, [fun EXCEPT ![i] = y], indices) =
         IF i \in indices
         THEN op(y, FoldFunctionOnSet(op, base, fun, indices \ {i}))
         ELSE FoldFunctionOnSet(op, base, fun, indices)

(*************************************************************************)
(* For an AC operator `op` for which `base` is the neutral element,      *)
(* folding a function commutes with set union, for disjoint sets.        *)
(*************************************************************************)
THEOREM FoldFunctionOnSetDisjointUnion ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         \A t,u \in Typ : op(t,u) = op(u,t),
         \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
         \A t \in Typ : op(base, t) = t,
         NEW S, IsFiniteSet(S), NEW T, IsFiniteSet(T), S \cap T = {},
         NEW fun, \A i \in S \union T : fun[i] \in Typ
  PROVE FoldFunctionOnSet(op, base, fun, S \union T) =
        op(FoldFunctionOnSet(op, base, fun, S), FoldFunctionOnSet(op, base, fun, T))

(*************************************************************************)
(* Analogous theorems for FoldFunction. Note that the theorems about     *)
(* adding an index and about disjoint union do not make sense here.      *)
(*************************************************************************)
THEOREM FoldFunctionEmpty ==
  ASSUME NEW op(_,_), NEW base, NEW fun, DOMAIN fun = {}
  PROVE  FoldFunction(op, base, fun) = base 

THEOREM FoldFunctionNonempty ==
  ASSUME NEW op(_,_), NEW base, NEW fun, 
         DOMAIN fun # {}, IsFiniteSet(DOMAIN fun)
  PROVE  \E i \in DOMAIN fun : FoldFunction(op, base, fun) = 
            op(fun[i], FoldFunctionOnSet(op, base, fun, DOMAIN fun \ {i}))

THEOREM FoldFunctionType ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         NEW fun, IsFiniteSet(DOMAIN fun),
         \A i \in DOMAIN fun : fun[i] \in Typ
  PROVE FoldFunction(op, base, fun) \in Typ

THEOREM FoldFunctionAC ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         \A t,u \in Typ : op(t,u) = op(u,t),
         \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
         NEW fun, IsFiniteSet(DOMAIN fun), NEW i \in DOMAIN fun,
         \A j \in DOMAIN fun : fun[j] \in Typ
  PROVE FoldFunction(op, base, fun) =
        op(fun[i], FoldFunctionOnSet(op, base, fun, (DOMAIN fun) \ {i}))

THEOREM FoldFunctionACExcept ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         \A t,u \in Typ : op(t,u) = op(u,t),
         \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
         NEW fun, NEW i, NEW y \in Typ,
         IsFiniteSet(DOMAIN fun), 
         \A j \in DOMAIN fun : fun[j] \in Typ 
  PROVE  FoldFunction(op, base, [fun EXCEPT ![i] = y]) =
         IF i \in DOMAIN fun
         THEN op(y, FoldFunctionOnSet(op, base, fun, (DOMAIN fun) \ {i}))
         ELSE FoldFunction(op, base, fun)

(*************************************************************************)
(* Summing a function that returns natural numbers, resp. integers,      *)
(* yields a natural number, resp. an integer.                            *)
(*************************************************************************)
THEOREM SumFunctionOnSetNat ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices),
         \A i \in indices : fun[i] \in Nat 
  PROVE  SumFunctionOnSet(fun, indices) \in Nat

THEOREM SumFunctionOnSetInt ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices),
         \A i \in indices : fun[i] \in Int
  PROVE  SumFunctionOnSet(fun, indices) \in Int

(*************************************************************************)
(* Summing two functions that agree on all relevant indices yields the   *)
(* same result.                                                          *)
(*************************************************************************)
THEOREM SumFunctionOnSetEqual ==
  ASSUME NEW f, NEW g, NEW indices, IsFiniteSet(indices),
         \A i \in indices : f[i] = g[i]
  PROVE  SumFunctionOnSet(f, indices) = SumFunctionOnSet(g, indices)

(*************************************************************************)
(* Summing a function over the empty set is 0.                           *)
(*************************************************************************)
THEOREM SumFunctionOnSetEmpty ==
  ASSUME NEW fun 
  PROVE  SumFunctionOnSet(fun, {}) = 0

(*************************************************************************)
(* Summing a function over a non-empty set corresponds to the sum of     *)
(* element of the set and the sum of the function over the remainder.    *)
(*************************************************************************)
THEOREM SumFunctionOnSetNonempty ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices), NEW i \in indices,
         \A j \in indices : fun[j] \in Int
  PROVE  SumFunctionOnSet(fun, indices) = 
         fun[i] + SumFunctionOnSet(fun, indices \ {i})

\* reformulation in terms of adding an index
THEOREM SumFunctionOnSetAddIndex ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices), 
         NEW i, i \notin indices,
         \A j \in indices \union {i} : fun[j] \in Int
  PROVE  SumFunctionOnSet(fun, indices \union {i}) = 
         fun[i] + SumFunctionOnSet(fun, indices)

\* corresponding lemma for removing an index
THEOREM SumFunctionOnSetRemoveIndex ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices), NEW i \in indices,
         \A j \in indices : fun[j] \in Int
  PROVE  SumFunctionOnSet(fun, indices \ {i}) = 
         SumFunctionOnSet(fun, indices) - fun[i]

(*************************************************************************)
(* Reduce the sum of an EXCEPT to the sum of the original function.      *)
(*************************************************************************)
THEOREM SumFunctionOnSetExcept ==
  ASSUME NEW fun, NEW i, NEW y \in Int,
         NEW indices \in SUBSET (DOMAIN fun), IsFiniteSet(indices),
         \A j \in indices : fun[j] \in Int 
  PROVE  SumFunctionOnSet([fun EXCEPT ![i] = y], indices) =
         IF i \in indices
         THEN SumFunctionOnSet(fun, indices) + y - fun[i]
         ELSE SumFunctionOnSet(fun, indices)

(*************************************************************************)
(* Summing a function distributes over disjoint union.                   *)
(*************************************************************************)
THEOREM SumFunctionOnSetDisjointUnion ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW T, IsFiniteSet(T), S \cap T = {},
         NEW fun, \A x \in S \union T : fun[x] \in Int 
  PROVE  SumFunctionOnSet(fun, S \union T) =
         SumFunctionOnSet(fun, S) + SumFunctionOnSet(fun, T)

(*************************************************************************)
(* Summing a Nat-valued function is monotonic in the subset relation.    *)
(*************************************************************************)
THEOREM SumFunctionNatOnSubset ==
  ASSUME NEW S, IsFiniteSet(S), NEW T \in SUBSET S,
         NEW fun, \A s \in S : fun[s] \in Nat
  PROVE  SumFunctionOnSet(fun, T) <= SumFunctionOnSet(fun, S)

(*************************************************************************)
(* The sum of a Nat-valued function is zero iff all relevant function    *)
(* values are zero.                                                      *)
(*************************************************************************)
THEOREM SumFunctionOnSetZero ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW fun, \A x \in S : fun[x] \in Nat
  PROVE  SumFunctionOnSet(fun, S) = 0 <=> \A x \in S : fun[x] = 0

(*************************************************************************)
(* Summing a function is monotonic in the function argument.             *)
(*************************************************************************)
THEOREM SumFunctionOnSetMonotonic ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW f, \A s \in S : f[s] \in Int,
         NEW g, \A s \in S : g[s] \in Int,
         \A s \in S : f[s] <= g[s]
  PROVE  SumFunctionOnSet(f, S) <= SumFunctionOnSet(g, S)

(*************************************************************************)
(* The sum over function f is strictly smaller than the sum over g if    *)
(* f[x] <= g[x] for all x \in S and f[x] < g[s] holds for at least some  *)
(* element s \in S.                                                      *)
(*************************************************************************)
THEOREM SumFunctionOnSetStrictlyMonotonic ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW f, \A s \in S : f[s] \in Int,
         NEW g, \A s \in S : g[s] \in Int,
         \A x \in S : f[x] <= g[x],
         NEW s \in S, f[s] < g[s]
  PROVE  SumFunctionOnSet(f, S) < SumFunctionOnSet(g, S)

(*************************************************************************)
(* Similar theorems for SumFunction.                                     *)
(*************************************************************************)
THEOREM SumFunctionNat ==
  ASSUME NEW fun, IsFiniteSet(DOMAIN fun),
         \A x \in DOMAIN fun : fun[x] \in Nat 
  PROVE  SumFunction(fun) \in Nat

THEOREM SumFunctionInt ==
  ASSUME NEW fun, IsFiniteSet(DOMAIN fun),
         \A x \in DOMAIN fun : fun[x] \in Int 
  PROVE  SumFunction(fun) \in Int 

THEOREM SumFunctionEmpty ==
  ASSUME NEW fun, DOMAIN fun = {}
  PROVE  SumFunction(fun) = 0

THEOREM SumFunctionNonempty ==
  ASSUME NEW fun, IsFiniteSet(DOMAIN fun), NEW x \in DOMAIN fun,
         \A i \in DOMAIN fun : fun[i] \in Int
  PROVE  SumFunction(fun) = fun[x] + SumFunctionOnSet(fun, (DOMAIN fun) \ {x})

THEOREM SumFunctionExcept ==
  ASSUME NEW fun, NEW i, NEW y \in Int, IsFiniteSet(DOMAIN fun),
         \A x \in DOMAIN fun : fun[x] \in Int 
  PROVE  SumFunction([fun EXCEPT ![i] = y]) =
         IF i \in DOMAIN fun 
         THEN SumFunction(fun) + y - fun[i]
         ELSE SumFunction(fun)

THEOREM SumFunctionZero ==
  ASSUME NEW fun, IsFiniteSet(DOMAIN fun), 
         \A x \in DOMAIN fun : fun[x] \in Nat
  PROVE  SumFunction(fun) = 0 <=> \A x \in DOMAIN fun : fun[x] = 0

THEOREM SumFunctionMonotonic ==
  ASSUME NEW f, IsFiniteSet(DOMAIN f), NEW g, DOMAIN g = DOMAIN f,
         \A x \in DOMAIN f : f[x] \in Int,
         \A x \in DOMAIN f : g[x] \in Int,
         \A x \in DOMAIN f : f[x] <= g[x]
  PROVE  SumFunction(f) <= SumFunction(g)

THEOREM SumFunctionStrictlyMonotonic ==
  ASSUME NEW f, IsFiniteSet(DOMAIN f), NEW g, DOMAIN g = DOMAIN f,
         \A x \in DOMAIN f : f[x] \in Int,
         \A x \in DOMAIN f : g[x] \in Int,
         \A x \in DOMAIN f : f[x] <= g[x],
         NEW s \in DOMAIN f, f[s] < g[s]
  PROVE  SumFunction(f) < SumFunction(g)

=============================================================================
\* Created Thu Apr 11 10:36:10 PDT 2013 by tomr
