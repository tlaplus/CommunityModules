--------------------- MODULE FunctionTheorems_proofs ------------------------
(***************************************************************************)
(* `^{\large \vspace{12pt}                                                 *)
(*  Proofs of facts about functions.                                       *)
(*  Originally contributed by Tom Rodeheffer, MSR.                         *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

EXTENDS Functions, Integers, NaturalsInduction, WellFoundedInduction, 
        FiniteSetTheorems, FoldsTheorems, TLAPS

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
BY DEF Restrict

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
BY DEF Range, Surjection


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
BY DEF Inverse, Range


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
BY DEF Injection, IsInjective


THEOREM Fun_IsSurj ==
  ASSUME NEW S, NEW T, NEW F \in [S -> T],
         \A t \in T : \E s \in S : F[s] = t
  PROVE  F \in Surjection(S,T)
BY DEF Surjection


THEOREM Fun_IsBij ==
  ASSUME NEW S, NEW T, NEW F,
         \/ F \in Injection(S,T)
         \/ (F \in [S -> T] /\ \A a,b \in S : F[a] = F[b] => a = b),

         \/ F \in Surjection(S,T)
         \/ (F \in [S -> T] /\ \A t \in T : \E s \in S : F[s] = t)
  PROVE  F \in Bijection(S,T)
BY DEF Bijection, Injection, IsInjective, Surjection




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
BY DEF Injection, IsInjective


THEOREM Fun_SurjectionProperties ==
  ASSUME NEW S, NEW T, NEW F \in Surjection(S,T)
  PROVE  /\ F \in [S -> T]
         /\ \A t \in T : \E s \in S : F[s] = t
         /\ Range(F) = T
BY DEF Surjection, Range


THEOREM Fun_BijectionProperties ==
  ASSUME NEW S, NEW T, NEW F \in Bijection(S,T)
  PROVE  /\ F \in [S -> T]
         /\ F \in Injection(S,T)
         /\ F \in Surjection(S,T)
         /\ \A a,b \in S : F[a] = F[b] => a = b
         /\ \A t \in T : \E s \in S : F[s] = t
BY DEF Bijection, Injection, IsInjective, Surjection



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
<1>1. f \in [S -> T]
  BY Fun_SurjectionProperties
<1>2. SUFFICES ASSUME f \notin Injection(S,T) PROVE FALSE
  BY Fun_IsBij
<1>3. PICK a,b \in S : a # b /\ f[a] = f[b]
  BY <1>1, <1>2, Fun_IsInj
<1>.  DEFINE U == S \ {b}
<1>4. U \in SUBSET S /\ U # S
  OBVIOUS
<1>.  DEFINE g == [x \in U |-> f[x]]
<1>5. g \in Surjection(U,T)
  <2>1. g \in [U -> T] BY <1>1
  <2>2. ASSUME NEW t \in T PROVE \E u \in U : g[u] = t
    <3>1. CASE t = f[b] BY <1>3, <3>1
    <3>2. CASE t # f[b]
      <4>1. PICK s \in S : f[s] = t
        BY Fun_SurjectionProperties
      <4>2. s \in U BY <3>2, <4>1
      <4>. QED BY <4>1, <4>2
    <3>3. QED BY <3>1, <3>2
  <2>3. QED BY <2>1, <2>2, Fun_IsSurj
<1>. QED BY <1>4, <1>5



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
BY DEF Injection, IsInjective


THEOREM Fun_SurjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Surjection(S,T),
         NEW G \in Surjection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Surjection(S,U)
BY Zenon DEF Surjection


THEOREM Fun_BijTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Bijection(S,T),
         NEW G \in Bijection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Bijection(S,U)
BY Fun_SurjTransitive, Fun_InjTransitive, Zenon DEF Bijection



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
BY DEF Inverse, Surjection, Injection, IsInjective, Range


THEOREM Fun_InjInverse ==
  ASSUME NEW S, NEW T, NEW f \in Injection(S,T), S = {} => T = {}
  PROVE  Inverse(f,S,T) \in Surjection(T,S)
<1>. DEFINE g == Inverse(f,S,T)
<1>1. f \in [S -> T]  BY DEF Injection, IsInjective
<1>2. g \in [T -> S]  BY <1>1, Fun_InverseProperties, Zenon
<1>3. ASSUME NEW s \in S  PROVE \E t \in T : g[t] = s
  <2>10. g[f[s]] = s  BY DEF Inverse, Range, Injection, IsInjective
  <2>. QED  BY <2>10, <1>1
<1>. QED  BY <1>2, <1>3 DEF Surjection


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

<1>. DEFINE g == Inverse(f,S,T)
<1>1. f \in [S -> T]  BY DEF Bijection, Injection
<1>2. f \in Surjection(S,T)  BY DEF Bijection
<1>3. \A a,b \in S : f[a] = f[b] => a = b  BY DEF Bijection, Injection, IsInjective
<1>4. g \in Injection(T,S)  BY <1>2, Fun_SurjInverse

<1>5. \A t \in T : f[g[t]] = t  BY <1>2 DEF Surjection, Inverse, Range
<1>6. \A s \in S : g[f[s]] = s  BY <1>1, <1>3 DEF Inverse, Range

<1>7. \A a,b \in T : g[a] = g[b] => a = b  BY <1>5
<1>8. \A s \in S : \E t \in T : g[t] = s  BY <1>1, <1>6

<1>9. g \in Bijection(T,S)  BY <1>4, <1>8 DEF Bijection, Injection, Surjection

<1>10. Inverse(g,T,S) = f
  <2>1. ASSUME NEW s \in S  PROVE f[s] = CHOOSE t \in T : s \in Range(g) => g[t] = s
    <3>1. PICK a \in T : g[a] = s  BY <1>9 DEF Bijection, Surjection
    <3>2. \A b \in T : g[b] = s => a = b  BY <3>1, <1>7
    <3>3. f[s] = a  BY <3>1, <1>5
    <3>4. s \in Range(g)  BY <3>1, <1>4 DEF Injection, Range
    <3>. QED  BY <3>1, <3>2, <3>3, <3>4
  <2>. QED  BY <2>1, <1>1 DEF Inverse
<1>. QED  BY <1>9, <1>6, <1>10

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
BY DEF Bijection, Injection, IsInjective, Surjection, Range, Restrict



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
BY DEF Bijection, Injection, IsInjective, Surjection, Range




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
BY DEF ExistsInjection


THEOREM Fun_ExistsSurj ==
  \A S,T : ExistsSurjection(S,T)  <=>  Surjection(S,T) # {}
BY DEF ExistsSurjection


THEOREM Fun_ExistsBij ==
  \A S,T : ExistsBijection(S,T)  <=>  Bijection(S,T) # {}
BY DEF ExistsBijection




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
<1>. PICK x \in T : TRUE  OBVIOUS
<1>. [s \in S |-> IF s \in T THEN s ELSE x] \in Surjection(S,T)
  BY DEF Surjection
<1>. QED  BY DEF ExistsSurjection




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
BY Fun_SurjInverse DEF ExistsSurjection, ExistsInjection



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
<1>. [s \in S |-> s] \in Bijection(S,S)  BY DEF Bijection, Injection, IsInjective, Surjection
<1>. QED  BY DEF ExistsBijection


THEOREM Fun_ExistsBijSymmetric ==
  ASSUME NEW S, NEW T, ExistsBijection(S,T)
  PROVE  ExistsBijection(T,S)
BY Fun_BijInverse DEF ExistsBijection


THEOREM Fun_ExistsBijTransitive ==
  ASSUME NEW S, NEW T, NEW U, ExistsBijection(S,T), ExistsBijection(T,U)
  PROVE  ExistsBijection(S,U)
BY Fun_BijTransitive, Zenon DEF ExistsBijection



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
BY Fun_ExistsBijReflexive DEF ExistsBijection, ExistsInjection, Bijection


THEOREM Fun_ExistsSurjReflexive ==
  ASSUME NEW S
  PROVE  ExistsSurjection(S,S)
BY Fun_ExistsBijReflexive DEF ExistsBijection, ExistsSurjection, Bijection


THEOREM Fun_ExistsInjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         ExistsInjection(S,T), ExistsInjection(T,U)
  PROVE  ExistsInjection(S,U)
BY Fun_InjTransitive, Zenon DEF ExistsInjection


THEOREM Fun_ExistsSurjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         ExistsSurjection(S,T), ExistsSurjection(T,U)
  PROVE  ExistsSurjection(S,U)
BY Fun_SurjTransitive, Zenon DEF ExistsSurjection


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
<1> PICK F \in Injection(S,T) : TRUE  BY Fun_ExistsInj

<1>1. /\ F \in [S -> T]
      /\ \A a,b \in S : F[a] = F[b] => a = b
  BY Fun_InjectionProperties

(*************************************************************************)
(* Pick Y as S excluding T.                                              *)
(*************************************************************************)
<1>2. PICK Y : Y = S \ T  BY Zenon

(*************************************************************************)
(* Define Ci[0] as Y, and Ci[i+1] as the image of Ci[i] under F.         *)
(*************************************************************************)
<1> DEFINE Ci[i \in Nat] ==
      IF i = 0 THEN Y ELSE {F[s] : s \in Ci[i-1]}
<1> HIDE DEF Ci

<1>3. \A i \in Nat : Ci[i] = IF i = 0 THEN Y ELSE {F[s] : s \in Ci[i-1]}
  (***********************************************************************)
  (* Use NatInductiveDef to prove that Ci equals its definition.         *)
  (***********************************************************************)
  <2> DEFINE
      f0       == Y
      Def(v,i) == {F[s] : s \in v}
      f        == CHOOSE f : f = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(f[i-1],i)]
  <2> SUFFICES \A i \in Nat : f[i] = IF i = 0 THEN f0 ELSE Def(f[i-1],i)  BY DEF Ci
  <2> HIDE DEF f0, Def, f
  <2> SUFFICES NatInductiveDefConclusion(f,f0,Def)  BY DEF NatInductiveDefConclusion
  <2> SUFFICES NatInductiveDefHypothesis(f,f0,Def)  BY NatInductiveDef, Zenon
  <2> QED BY Zenon DEF NatInductiveDefHypothesis, f

(*************************************************************************)
(* Applying F to an element of Ci[i] produces an element of Ci[i+1].     *)
(*************************************************************************)
<1>4. ASSUME NEW i \in Nat, NEW s \in Ci[i]
      PROVE F[s] \in Ci[i+1]
   BY <1>3

(*************************************************************************)
(* Each element of Ci[i+1] is the application of F to some element in    *)
(* Ci[i].                                                                *)
(*************************************************************************)
<1>5. ASSUME NEW i \in Nat, NEW t \in Ci[i+1]
      PROVE \E s \in Ci[i] : F[s] = t
   <2>1. Ci[i+1] = {F[s] : s \in Ci[i]}
     BY <1>3, i+1 \in Nat \ {0}, (i+1)-1 = i, Zenon
   <2>. QED  BY <2>1

(*************************************************************************)
(* Each Ci[i] \subseteq S.                                               *)
(*************************************************************************)
<1>6. \A i \in Nat : Ci[i] \subseteq S
  <2> DEFINE Prop(i) == Ci[i] \subseteq S
  <2> SUFFICES \A i \in Nat : Prop(i)  OBVIOUS
  <2>1. Prop(0)  BY <1>2, <1>3, Zenon
  <2>2. ASSUME NEW i \in Nat, Prop(i)  PROVE Prop(i+1)
    <3> SUFFICES ASSUME NEW t \in Ci[i+1]  PROVE t \in S  OBVIOUS
    <3>1. PICK s \in Ci[i] : F[s] = t  BY <1>5
    <3>2. s \in S  BY <2>2
    <3> QED BY <3>1, <3>2, <1>1
  <2> HIDE DEF Prop
  <2> QED BY <2>1, <2>2, NatInduction, Isa

(*************************************************************************)
(* Pick C as the union of all Ci[i].                                     *)
(*************************************************************************)
<1>7. PICK C : C = UNION {Ci[i] : i \in Nat}  OBVIOUS
<1>8. C \subseteq S  BY <1>6, <1>7

(*************************************************************************)
(* Pick FC as the image of C under F.                                    *)
(*************************************************************************)
<1>9. PICK FC : FC = {F[c] : c \in C}  BY Zenon
<1>10. FC \subseteq T  BY <1>1, <1>8, <1>9

(*************************************************************************)
(* C = Y \cup FC because Ci[0] = Y and Ci[i+1] = image of Ci[i] under F. *)
(*************************************************************************)
<1>11. C = Y \cup FC
  <2>1. ASSUME NEW c \in C  PROVE c \in Y \cup FC
    <3>1. PICK i \in Nat : c \in Ci[i]  BY <1>7
    <3>2. CASE i = 0  BY <3>1, <3>2, <1>3, Zenon
    <3>3. CASE i > 0
      <4>0. i-1 \in Nat
        BY <3>3
      <4>1. PICK s \in Ci[i-1] : F[s] = c
        BY <4>0, <3>1, <1>5
      <4>2. s \in C  BY <3>3, <1>7
      <4> QED BY <4>1, <4>2, <1>9
    <3> QED BY <3>2, <3>3
  <2>2. ASSUME NEW c \in Y \cup FC  PROVE c \in C
    <3>1. CASE c \in Y  BY <3>1, <1>3, <1>7, Zenon
    <3>2. CASE c \in FC
      <4>1. PICK s \in C : F[s] = c  BY <3>2, <1>9
      <4>2. PICK i \in Nat : s \in Ci[i]  BY <4>1, <1>7
      <4>3. F[s] \in Ci[i+1]  BY <4>2, <1>4
      <4> QED BY <4>1, <4>3, <1>7
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2

(*************************************************************************)
(* S \ C is the same as T \ FC.                                          *)
(*************************************************************************)
<1>12. S \ C = T \ FC  BY <1>2, <1>11

(*************************************************************************)
(* Pick H as F on C and the identity on S \ C.  Since F (restricted to   *)
(* C) is a bijection from C to FC and S \ C = T \ FC, this makes H a     *)
(* bijection from S to T.                                                *)
(*************************************************************************)
<1>13. PICK H : H = [s \in S |-> IF s \in C THEN F[s] ELSE s]  OBVIOUS
<1>14. H \in Bijection(S,T)
  (***********************************************************************)
  (* A useful lemma.  If a \in C and b \notin C, then H[a] # H[b].       *)
  (***********************************************************************)
  <2>1. ASSUME NEW a \in S, NEW b \in S, a \in C, b \notin C  PROVE H[a] # H[b]
    <3>1. H[a] \in FC  BY <2>1, <1>1, <1>9, <1>13
    <3>2. H[b] \in T \ FC  BY <2>1, <1>12, <1>13
    <3> QED BY <3>1, <3>2

  <2>2. H \in [S -> T]
    <3> SUFFICES ASSUME NEW s \in S  PROVE H[s] \in T  BY <1>13
    <3>1. CASE s \in C  BY <3>1, <1>1, <1>10, <1>13
    <3>2. CASE s \notin C  BY <3>2, <1>12, <1>13
    <3> QED BY <3>1, <3>2

  <2>3. ASSUME NEW a \in S, NEW b \in S, H[a] = H[b]  PROVE a = b
    <3> H[a] = H[b]  BY <2>3
    <3>1. CASE a \in C /\ b \in C  BY <3>1, <1>1, <1>13
    <3>2. CASE a \in C /\ b \notin C  BY <3>2, <2>1  (* impossible by lemma *)
    <3>3. CASE a \notin C /\ b \in C  BY <3>3, <2>1  (* impossible by lemma *)
    <3>4. CASE a \notin C /\ b \notin C  BY <3>4, <1>13
    <3> QED BY <3>1, <3>2, <3>3, <3>4

  <2>4. ASSUME NEW t \in T  PROVE \E s \in S : H[s] = t
    <3>1. CASE t \in FC  BY <3>1, <1>8, <1>9, <1>13
    <3>2. CASE t \notin FC  BY <3>2, <1>12, <1>13
    <3> QED BY <3>1, <3>2

  <2> QED BY <2>2, <2>3, <2>4, Fun_IsBij

<1> QED BY <1>14, Fun_ExistsBij





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

<1>1. PICK F : F \in Injection(S,T)  BY DEF ExistsInjection
<1>2. PICK G : G \in Injection(T,S)  BY DEF ExistsInjection
<1>. DEFINE GF == [s \in S |-> G[F[s]]]
<1>3. Range(G) \subseteq S  BY <1>2, Fun_RangeProperties DEF Injection
<1>4. GF \in Injection(S, Range(G))  BY <1>1, <1>2 DEF Injection, IsInjective, Range
<1>5. ExistsBijection(S, Range(G))
  BY <1>3, <1>4, Fun_CantorBernsteinSchroeder_Lemma DEF ExistsInjection
<1>6. ExistsBijection(T, Range(G))
  BY <1>2, Fun_InjMeansBijImage DEF ExistsBijection
<1>. QED  BY <1>5, <1>6, Fun_ExistsBijSymmetric, Fun_ExistsBijTransitive



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
<1>. ExistsInjection(T,S)  BY Fun_SurjInverse DEF ExistsInjection, ExistsSurjection
<1>. QED  BY Fun_CantorBernsteinSchroeder



THEOREM Fun_ExistSurjAndSurjThenBij ==
  ASSUME NEW S, NEW T,
         ExistsSurjection(S,T), ExistsSurjection(T,S)
  PROVE  ExistsBijection(S,T)
<1>. ExistsInjection(S,T)  BY Fun_SurjInverse DEF ExistsInjection, ExistsSurjection
<1>2. QED  BY Fun_ExistInjAndSurjThenBij




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

<1>1. ExistsBijection(S,T) <=> ExistsBijection(T,S)
  BY Fun_ExistsBijSymmetric
<1>2. ExistsInjection(S,T) /\ ExistsInjection(T,S) => ExistsBijection(S,T)
  BY Fun_CantorBernsteinSchroeder
<1>3. \A S1, T1 :  ExistsBijection(S1,T1) => ExistsSurjection(S1,T1)
  BY DEF ExistsBijection, ExistsSurjection, Bijection
<1>4. \A S1,T1 : ExistsSurjection(S1,T1) => ExistsInjection(T1,S1)
  BY Fun_ExistsSurjMeansExistsRevInj
<1> QED BY <1>1, <1>2, <1>3, <1>4


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

<1>. DEFINE f == [i \in 1 .. b-a+1 |-> i+a-1]
<1>1. f \in [1 .. b-a+1 -> a .. b]  BY SMT
<1>2. f \in Injection(1 .. b-a+1, a .. b) BY DEF Injection, IsInjective
<1>3. \A t \in a..b :
         /\ t-a+1 \in 1 .. (b-a+1)
         /\ f[t-a+1] = t
  OBVIOUS
<1>4. f \in Surjection(1 .. b-a+1, a .. b)
  BY <1>3, <1>1, Zenon DEF Surjection
<1>. QED  BY <1>1, <1>2, <1>4 DEF ExistsBijection, Bijection


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
(*************************************************************************)
(* n \leq m means Injection exists.  This part is easy.                  *)
(*************************************************************************)
<1>1. ASSUME n \leq m PROVE [i \in 1..n |-> i] \in Injection(1..n, 1..m)
  BY <1>1 DEF Injection, IsInjective

(*************************************************************************)
(* Injection exists means n \leq m.  This part is harder.                *)
(*************************************************************************)
<1>2. ASSUME ExistsInjection(1..n,1..m)  PROVE n \leq m
  <2>. DEFINE P(mm) == \A nn \in Nat : nn > mm => Injection(1..nn, 1..mm) = {}
  <2>1. SUFFICES \A mm \in Nat : P(mm)
    BY <1>2 DEF ExistsInjection
  <2>2. P(0)
    <3>. SUFFICES ASSUME NEW nn \in Nat, nn > 0
                  PROVE  Injection(1..nn, 1..0) = {}
      OBVIOUS
    <3>1. /\ 1 .. nn # {}
          /\ 1 .. 0 = {}
      BY Isa
    <3>. QED  BY <3>1 DEF Injection
  <2>3. ASSUME NEW mm \in Nat, P(mm)  PROVE P(mm+1)
    <3>1. SUFFICES ASSUME NEW nn \in Nat, nn > mm+1,
                          NEW f \in Injection(1..nn, 1..mm+1)
                   PROVE  FALSE
      OBVIOUS
    <3>2. ASSUME NEW i \in 1..nn, f[i] = mm+1 PROVE FALSE
      <4>. DEFINE g == [j \in 1..nn-1 |-> IF j<i THEN f[j] ELSE f[j+1]]
      <4>1. nn-1 \in Nat /\ nn-1 > mm  BY <3>1
      <4>2. g \in Injection(1..nn-1, 1..mm)  BY <3>2 DEF Injection, IsInjective
      <4>. QED  BY <4>1, <4>2, P(mm), Zenon DEF Injection
    <3>3. ASSUME ~\E i \in 1..nn : f[i] = mm+1  PROVE FALSE
      <4>. f \in Injection(1..nn, 1..mm)  BY <3>3 DEF Injection
      <4>. QED  BY <3>1, P(mm)
    <3>. QED  BY <3>2, <3>3
  <2>. QED  BY NatInduction, <2>2, <2>3, Isa

<1> QED BY <1>1, <1>2 DEF ExistsInjection






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

  (*************************************************************************)
  (* Pick the smallest m \in Nat for which there is a surjection from      *)
  (* 1..m to S.                                                            *)
  (*************************************************************************)
<1>1. PICK m \in Nat :
        /\ ExistsSurjection(1..m, S)
        /\ \A k \in Nat : k < m => ~ExistsSurjection(1..k, S)
  <2>. DEFINE NN == { m \in Nat : ExistsSurjection(1..m, S) }
  <2>1. PICK m \in NN : \A k \in NN : <<k, m>> \notin OpToRel(<, Nat)
     BY WFMin, NatLessThanWellFounded, Zenon
  <2>. QED
    BY <2>1, Zenon DEF OpToRel

<1>2. m <= n  BY <1>1
  (*************************************************************************)
  (* Any surjection from 1..m to S is bijective.                           *)
  (*************************************************************************)
<1>3. PICK f \in Surjection(1..m, S) : TRUE  BY <1>1 DEF ExistsSurjection
<1>4. ASSUME f \notin Injection(1..m, S)  PROVE FALSE
  <2>1. f \in [1..m -> S]  BY <1>3 DEF Surjection
  <2>2. PICK i,j \in 1..m : i < j /\ f[i] = f[j]
    <3>1. PICK ii,jj \in 1..m : ii # jj /\ f[ii] = f[jj]
      BY <2>1, <1>4 DEF Injection, IsInjective
    <3>2. CASE ii < jj  BY <3>1, <3>2
    <3>3. CASE jj < ii  BY <3>1, <3>3
    <3>. QED  BY SMT, <3>1, <3>2, <3>3
  <2>3. m-1 \in Nat  BY <2>2
  <2>. DEFINE g == [k \in 1..m-1 |-> IF k=j THEN f[m] ELSE f[k]]
  <2>4. g \in Surjection(1..m-1, S)
    <3>1. g \in [1..m-1 -> S]  BY <2>1
    <3>2. ASSUME NEW s \in S  PROVE \E k \in 1..m-1 : g[k] = s
      <4>. PICK l \in 1..m : f[l] = s  BY <1>3 DEF Surjection
      <4>1. CASE l = j
        BY <2>2, <4>1, i \in 1 .. m-1
      <4>2. CASE l # j /\ l = m
        BY <4>2, j \in 1 .. m-1
      <4>3. CASE l # j /\ l # m
        BY <4>3
      <4>. QED  BY <4>1, <4>2, <4>3
    <3>. QED  BY <3>1, <3>2, Zenon DEF Surjection
  <2>. QED  BY SMT, <2>3, <2>4, <1>1 DEF ExistsSurjection

<1>. QED  BY <1>2, <1>3, <1>4 DEF ExistsBijection, Bijection


(***************************************************************************)
(* Simple corollary.                                                       *)
(***************************************************************************)
THEOREM Fun_NatSurjEquivNatBij ==
  ASSUME NEW S
  PROVE  (\E n \in Nat : ExistsSurjection(1..n,S))
    <=>  (\E m \in Nat : ExistsBijection(1..m,S))
BY Fun_NatSurjImpliesNatBij, Fun_ExistsBijEquiv



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
BY Fun_NatInjLeq, Fun_ExistsBijEquiv, Fun_ExistsBijTransitive



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

<1>1. ASSUME ExistsBijection(1..0, S), S # {} PROVE FALSE
  <2>. ExistsInjection(S, 1..0)  BY <1>1, Fun_ExistsBijEquiv
  <2>. QED  BY <1>1 DEF ExistsInjection, Injection
<1>2. ASSUME S = {}  PROVE ExistsBijection(1..0, S)
  BY <1>2, Fun_ExistsBijReflexive, Isa
<1>3. QED  BY <1>1, <1>2


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
<1>1. ASSUME NEW f \in Bijection(1..1, S)  PROVE \E s : S = {s}
  BY 1..1 = {1} DEF Bijection, Surjection
<1>2. ASSUME NEW s, S = {s}  PROVE [i \in 1..1 |-> s] \in Bijection(1..1, S)
  BY <1>2 DEF Bijection, Injection, IsInjective, Surjection
<1>. QED  BY <1>1, <1>2 DEF ExistsBijection


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

<1>1. CASE T = {}  BY <1>1, Fun_NatBijEmpty
<1>2. CASE T # {}
  <2>0. ExistsSurjection(1..m, S)  BY Fun_ExistsBijEquiv
  <2>1. ExistsSurjection(S, T)  BY <1>2, Fun_ExistsSurjSubset
  <2>2. ExistsSurjection(1..m, T)  BY <2>0, <2>1, Fun_ExistsSurjTransitive
  <2>. QED  BY <2>2, Fun_NatSurjImpliesNatBij
<1> QED BY <1>1, <1>2




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

<1>1. PICK F \in Bijection(1..m, S) : TRUE  BY DEF ExistsBijection
<1>2. F \in [1..m -> S]  BY <1>1 DEF Bijection, Injection
<1>3. \A s \in S : \E i \in 1..m : F[i] = s  BY <1>1 DEF Bijection, Surjection
<1>4. \A i,j \in 1..m : F[i] = F[j] => i = j  BY <1>1 DEF Bijection, Injection, IsInjective

<1>. DEFINE G == [i \in 1..m+1 |-> IF i <= m THEN F[i] ELSE x]
<1>10. G \in [1..m+1 -> S \cup {x}]  BY SMT, <1>2
<1>20. ASSUME NEW t \in S \cup {x}  PROVE \E i \in 1..m+1 : G[i] = t
  <2>1. CASE t \in S 
    BY <1>3, <2>1, 1..m \subseteq 1 .. m+1
  <2>2. CASE t = x
    BY <2>2, m+1 \in 1 .. m+1
  <2>. QED  BY <2>1, <2>2
<1>30. ASSUME NEW i \in 1..m+1, NEW j \in 1..m+1, G[i] = G[j]  PROVE i = j
  BY <1>2, <1>4, <1>30
<1>40. G \in Bijection(1..m+1, S \cup {x})
  BY <1>10, <1>20, <1>30, Zenon DEF Bijection, Injection, IsInjective, Surjection
<1>. QED  BY <1>40, Zenon DEF ExistsBijection




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

<1>1. PICK n \in Nat : ExistsBijection(1..n, S \ {x})  BY Fun_NatBijSubset, Zenon
<1>2. ExistsBijection(1..n+1, (S \ {x}) \cup {x})  BY <1>1, Fun_NatBijAddElem, Zenon
<1>3. ExistsBijection(1..n+1, S)  BY <1>2, Zenon
<1>4. n = m-1  BY <1>3, Fun_NatBijSame
<1>. QED  BY <1>1, <1>4

(***************************************************************************)
(* Folding a function for an empty set of indices yields the base value.   *)
(***************************************************************************)
THEOREM FoldFunctionOnSetEmpty ==
  ASSUME NEW op(_,_), NEW base, NEW fun
  PROVE  FoldFunctionOnSet(op, base, fun, {}) = base 
BY MapThenFoldSetEmpty, Zenon DEF FoldFunctionOnSet

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
<1>1. \A T : T # {} => (CHOOSE t \in T : TRUE) \in T 
  OBVIOUS
<1>. QED  BY <1>1, MapThenFoldSetNonempty, Isa DEF FoldFunctionOnSet

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
<1>1. \A T : T # {} => (CHOOSE t \in T : TRUE) \in T 
  OBVIOUS
<1>. QED  BY <1>1, MapThenFoldSetType, Isa DEF FoldFunctionOnSet

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
<1>1. \A T : T # {} => (CHOOSE t \in T : TRUE) \in T 
  OBVIOUS
<1>. QED  BY <1>1, MapThenFoldSetEqual, Isa DEF FoldFunctionOnSet

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
<1>1. \A T : T # {} => (CHOOSE t \in T : TRUE) \in T 
  OBVIOUS
<1>. QED  BY <1>1, MapThenFoldSetAC, Isa DEF FoldFunctionOnSet

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
<1>1. \A T : T # {} => (CHOOSE t \in T : TRUE) \in T 
  OBVIOUS
<1>. QED  BY <1>1, MapThenFoldSetACAddElement, Isa DEF FoldFunctionOnSet

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
<1>. DEFINE g == [fun EXCEPT ![i] = y]
<1>1. \A j \in indices \ {i} : g[j] = fun[j]
  OBVIOUS 
<1>2. IsFiniteSet(indices \ {i})
    BY FS_RemoveElement
<1>3. CASE i \in indices
  <2>1. \A j \in indices : g[j] \in Typ 
    BY <1>3
  <2>2. FoldFunctionOnSet(op, base, g, indices) =
        op(g[i], FoldFunctionOnSet(op, base, g, indices \ {i}))
    BY <1>3, <2>1, FoldFunctionOnSetAC, Isa 
  <2>. QED  BY <1>1, <1>2, <1>3, <2>2, FoldFunctionOnSetEqual, Isa
<1>4. CASE i \notin indices
  <2>. QED BY <1>1, <1>2, <1>4, indices = indices \ {i}, FoldFunctionOnSetEqual, Isa
<1>. QED  BY <1>3, <1>4

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
<1>1. \A U : U # {} => (CHOOSE u \in U : TRUE) \in U 
  OBVIOUS
<1>. QED  BY <1>1, MapThenFoldSetDisjointUnion, Isa DEF FoldFunctionOnSet

(*************************************************************************)
(* Analogous theorems for FoldFunction. Note that the theorems about     *)
(* adding an index and about disjoint union do not make sense here.      *)
(*************************************************************************)
THEOREM FoldFunctionEmpty ==
  ASSUME NEW op(_,_), NEW base, NEW fun, DOMAIN fun = {}
  PROVE  FoldFunction(op, base, fun) = base 
BY FoldFunctionOnSetEmpty, Zenon DEF FoldFunction

THEOREM FoldFunctionNonempty ==
  ASSUME NEW op(_,_), NEW base, NEW fun, 
         DOMAIN fun # {}, IsFiniteSet(DOMAIN fun)
  PROVE  \E i \in DOMAIN fun : FoldFunction(op, base, fun) = 
            op(fun[i], FoldFunctionOnSet(op, base, fun, DOMAIN fun \ {i}))
BY FoldFunctionOnSetNonempty, Isa DEF FoldFunction

THEOREM FoldFunctionType ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         NEW fun, IsFiniteSet(DOMAIN fun),
         \A i \in DOMAIN fun : fun[i] \in Typ
  PROVE FoldFunction(op, base, fun) \in Typ
BY FoldFunctionOnSetType, Isa DEF FoldFunction 

THEOREM FoldFunctionAC ==
  ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
         \A t,u \in Typ : op(t,u) \in Typ,
         \A t,u \in Typ : op(t,u) = op(u,t),
         \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
         NEW fun, IsFiniteSet(DOMAIN fun), NEW i \in DOMAIN fun,
         \A j \in DOMAIN fun : fun[j] \in Typ
  PROVE FoldFunction(op, base, fun) =
        op(fun[i], FoldFunctionOnSet(op, base, fun, (DOMAIN fun) \ {i}))
BY FoldFunctionOnSetAC, Isa DEF FoldFunction 

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
BY FoldFunctionOnSetACExcept, Isa DEF FoldFunction 

(*************************************************************************)
(* Summing a function that returns natural numbers, resp. integers,      *)
(* yields a natural number, resp. an integer.                            *)
(*************************************************************************)
LEMMA IntegersAC ==
  /\ 0 \in Int 
  /\ \A x,y \in Int : x+y \in Int 
  /\ \A x,y \in Int : x+y = y+x
  /\ \A x,y,z \in Int : x + (y+z) = (x+y) + z
  /\ \A x \in Int : 0 + x = x
OBVIOUS

THEOREM SumFunctionOnSetNat ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices),
         \A i \in indices : fun[i] \in Nat 
  PROVE  SumFunctionOnSet(fun, indices) \in Nat
<1>. /\ 0 \in Nat 
     /\ \A x,y \in Nat : x + y \in Nat 
  OBVIOUS
<1>. QED  BY FoldFunctionOnSetType, IsaM("iprover") DEF SumFunctionOnSet

THEOREM SumFunctionOnSetInt ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices),
         \A i \in indices : fun[i] \in Int
  PROVE  SumFunctionOnSet(fun, indices) \in Int
BY FoldFunctionOnSetType, IntegersAC, IsaM("iprover") DEF SumFunctionOnSet

(*************************************************************************)
(* Summing two functions that agree on all relevant indices yields the   *)
(* same result.                                                          *)
(*************************************************************************)
THEOREM SumFunctionOnSetEqual ==
  ASSUME NEW f, NEW g, NEW indices, IsFiniteSet(indices),
         \A i \in indices : f[i] = g[i]
  PROVE  SumFunctionOnSet(f, indices) = SumFunctionOnSet(g, indices)
BY FoldFunctionOnSetEqual, Zenon DEF SumFunctionOnSet 

(*************************************************************************)
(* Summing a function over the empty set is 0.                           *)
(*************************************************************************)
THEOREM SumFunctionOnSetEmpty ==
  ASSUME NEW fun 
  PROVE  SumFunctionOnSet(fun, {}) = 0
BY FoldFunctionOnSetEmpty, Zenon DEF SumFunctionOnSet

(*************************************************************************)
(* Summing a function over a non-empty set corresponds to the sum of     *)
(* element of the set and the sum of the function over the remainder.    *)
(*************************************************************************)
THEOREM SumFunctionOnSetNonempty ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices), NEW i \in indices,
         \A j \in indices : fun[j] \in Int
  PROVE  SumFunctionOnSet(fun, indices) = 
         fun[i] + SumFunctionOnSet(fun, indices \ {i})
  BY FoldFunctionOnSetAC, IntegersAC, IsaM("iprover") DEF SumFunctionOnSet 

\* reformulation in terms of adding an index
THEOREM SumFunctionOnSetAddIndex ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices), 
         NEW i, i \notin indices,
         \A j \in indices \union {i} : fun[j] \in Int
  PROVE  SumFunctionOnSet(fun, indices \union {i}) = 
         fun[i] + SumFunctionOnSet(fun, indices)
BY FoldFunctionOnSetACAddIndex, IntegersAC, IsaM("iprover") DEF SumFunctionOnSet 

\* corresponding lemma for removing an index
THEOREM SumFunctionOnSetRemoveIndex ==
  ASSUME NEW fun, NEW indices, IsFiniteSet(indices), NEW i \in indices,
         \A j \in indices : fun[j] \in Int
  PROVE  SumFunctionOnSet(fun, indices \ {i}) = 
         SumFunctionOnSet(fun, indices) - fun[i]
<1>. IsFiniteSet(indices \ {i})
  BY FS_RemoveElement
<1>. QED  BY SumFunctionOnSetNonempty, SumFunctionOnSetInt

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
<1>1. SumFunctionOnSet([fun EXCEPT ![i] = y], indices) =
      IF i \in indices
      THEN y + SumFunctionOnSet(fun, indices \ {i})
      ELSE SumFunctionOnSet(fun, indices)
  BY FoldFunctionOnSetACExcept, IntegersAC, IsaM("iprover") DEF SumFunctionOnSet 
<1>2. i \in indices => 
      SumFunctionOnSet(fun, indices \ {i}) = SumFunctionOnSet(fun, indices) - fun[i]
  BY SumFunctionOnSetRemoveIndex
<1>3. SumFunctionOnSet(fun, indices) \in Int 
  BY SumFunctionOnSetInt
<1>. QED  BY <1>1, <1>2, <1>3

(*************************************************************************)
(* Summing a function distributes over disjoint union.                   *)
(*************************************************************************)
THEOREM SumFunctionOnSetDisjointUnion ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW T, IsFiniteSet(T), S \cap T = {},
         NEW fun, \A x \in S \union T : fun[x] \in Int 
  PROVE  SumFunctionOnSet(fun, S \union T) =
         SumFunctionOnSet(fun, S) + SumFunctionOnSet(fun, T)
BY FoldFunctionOnSetDisjointUnion, IntegersAC, IsaM("iprover") DEF SumFunctionOnSet 

(*************************************************************************)
(* Summing a Nat-valued function is monotonic in the subset relation.    *)
(*************************************************************************)
THEOREM SumFunctionNatOnSubset ==
  ASSUME NEW S, IsFiniteSet(S), NEW T \in SUBSET S,
         NEW fun, \A s \in S : fun[s] \in Nat
  PROVE  SumFunctionOnSet(fun, T) <= SumFunctionOnSet(fun, S)
<1>. DEFINE U == S \ T 
<1>1. /\ IsFiniteSet(T)
      /\ IsFiniteSet(U)
      /\ T \cap U = {}
      /\ S = T \union U
      /\ \A x \in T \union U : fun[x] \in Int 
  BY FS_Subset
<1>2. SumFunctionOnSet(fun, S) = SumFunctionOnSet(fun, T) + SumFunctionOnSet(fun, U)
  BY <1>1, SumFunctionOnSetDisjointUnion
<1>3. /\ SumFunctionOnSet(fun, T) \in Nat 
      /\ SumFunctionOnSet(fun, U) \in Nat 
  BY <1>1, SumFunctionOnSetNat
<1>. QED  BY <1>2, <1>3

(*************************************************************************)
(* The sum of a Nat-valued function is zero iff all relevant function    *)
(* values are zero.                                                      *)
(*************************************************************************)
THEOREM SumFunctionOnSetZero ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW fun, \A x \in S : fun[x] \in Nat
  PROVE  SumFunctionOnSet(fun, S) = 0 <=> \A x \in S : fun[x] = 0
<1>. DEFINE P(T) == SumFunctionOnSet(fun, T) = 0 <=> \A x \in T : fun[x] = 0
<1>1. P({})
  BY SumFunctionOnSetEmpty
<1>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), P(T), NEW x \in S \ T 
      PROVE  P(T \union {x})
  <2>1. SumFunctionOnSet(fun, T \union {x}) = fun[x] + SumFunctionOnSet(fun, T)
    BY <1>2, SumFunctionOnSetAddIndex
  <2>2. SumFunctionOnSet(fun, T) \in Nat
    BY <1>2, SumFunctionOnSetNat
  <2>. QED  BY <1>2, <2>1, <2>2
<1>. QED
  <2>. HIDE DEF P 
  <2>. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("iprover")
  <2>. QED   BY DEF P

(*************************************************************************)
(* Summing a function is monotonic in the function argument.             *)
(*************************************************************************)
THEOREM SumFunctionOnSetMonotonic ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW f, \A s \in S : f[s] \in Int,
         NEW g, \A s \in S : g[s] \in Int,
         \A s \in S : f[s] <= g[s]
  PROVE  SumFunctionOnSet(f, S) <= SumFunctionOnSet(g, S)
<1>. DEFINE P(T) == SumFunctionOnSet(f, T) <= SumFunctionOnSet(g, T)
<1>1. P({})
  BY SumFunctionOnSetEmpty
<1>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), P(T), NEW x \in S \ T 
      PROVE  P(T \union {x})
  <2>1. /\ SumFunctionOnSet(f, T \union {x}) = f[x] + SumFunctionOnSet(f, T)
        /\ SumFunctionOnSet(g, T \union {x}) = g[x] + SumFunctionOnSet(g, T)
    BY <1>2, SumFunctionOnSetAddIndex
  <2>2. /\ SumFunctionOnSet(f, T) \in Int 
        /\ SumFunctionOnSet(g, T) \in Int 
    BY <1>2, SumFunctionOnSetInt
  <2>. QED  BY <1>2, <2>1, <2>2
<1>. QED
  <2>. HIDE DEF P 
  <2>. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("iprover")
  <2>. QED   BY DEF P

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
<1>1. /\ SumFunctionOnSet(f, S) = f[s] + SumFunctionOnSet(f, S \ {s})
      /\ SumFunctionOnSet(g, S) = g[s] + SumFunctionOnSet(g, S \ {s})
  BY SumFunctionOnSetNonempty
<1>2. IsFiniteSet(S \ {s})
  BY FS_RemoveElement
<1>3. SumFunctionOnSet(f, S \ {s}) <= SumFunctionOnSet(g, S \ {s})
  BY <1>2, SumFunctionOnSetMonotonic
<1>4. /\ SumFunctionOnSet(f, S \ {s}) \in Int
      /\ SumFunctionOnSet(g, S \ {s}) \in Int
  BY <1>2, SumFunctionOnSetInt
<1>. QED  BY <1>1, <1>3, <1>4

(*************************************************************************)
(* Similar theorems for SumFunction.                                     *)
(*************************************************************************)
THEOREM SumFunctionNat ==
  ASSUME NEW fun, IsFiniteSet(DOMAIN fun),
         \A x \in DOMAIN fun : fun[x] \in Nat 
  PROVE  SumFunction(fun) \in Nat
BY SumFunctionOnSetNat DEF SumFunction 

THEOREM SumFunctionInt ==
  ASSUME NEW fun, IsFiniteSet(DOMAIN fun),
         \A x \in DOMAIN fun : fun[x] \in Int 
  PROVE  SumFunction(fun) \in Int 
BY SumFunctionOnSetInt DEF SumFunction 

THEOREM SumFunctionEmpty ==
  ASSUME NEW fun, DOMAIN fun = {}
  PROVE  SumFunction(fun) = 0
BY SumFunctionOnSetEmpty DEF SumFunction 

THEOREM SumFunctionNonempty ==
  ASSUME NEW fun, IsFiniteSet(DOMAIN fun), NEW x \in DOMAIN fun,
         \A i \in DOMAIN fun : fun[i] \in Int
  PROVE  SumFunction(fun) = fun[x] + SumFunctionOnSet(fun, (DOMAIN fun) \ {x})
BY SumFunctionOnSetNonempty DEF SumFunction

THEOREM SumFunctionExcept ==
  ASSUME NEW fun, NEW i, NEW y \in Int, IsFiniteSet(DOMAIN fun),
         \A x \in DOMAIN fun : fun[x] \in Int 
  PROVE  SumFunction([fun EXCEPT ![i] = y]) =
         IF i \in DOMAIN fun 
         THEN SumFunction(fun) + y - fun[i]
         ELSE SumFunction(fun)
BY SumFunctionOnSetExcept DEF SumFunction 

THEOREM SumFunctionZero ==
  ASSUME NEW fun, IsFiniteSet(DOMAIN fun), 
         \A x \in DOMAIN fun : fun[x] \in Nat
  PROVE  SumFunction(fun) = 0 <=> \A x \in DOMAIN fun : fun[x] = 0
BY SumFunctionOnSetZero DEF SumFunction 

THEOREM SumFunctionMonotonic ==
  ASSUME NEW f, IsFiniteSet(DOMAIN f), NEW g, DOMAIN g = DOMAIN f,
         \A x \in DOMAIN f : f[x] \in Int,
         \A x \in DOMAIN f : g[x] \in Int,
         \A x \in DOMAIN f : f[x] <= g[x]
  PROVE  SumFunction(f) <= SumFunction(g)
BY SumFunctionOnSetMonotonic DEF SumFunction 

THEOREM SumFunctionStrictlyMonotonic ==
  ASSUME NEW f, IsFiniteSet(DOMAIN f), NEW g, DOMAIN g = DOMAIN f,
         \A x \in DOMAIN f : f[x] \in Int,
         \A x \in DOMAIN f : g[x] \in Int,
         \A x \in DOMAIN f : f[x] <= g[x],
         NEW s \in DOMAIN f, f[s] < g[s]
  PROVE  SumFunction(f) < SumFunction(g)
BY SumFunctionOnSetStrictlyMonotonic DEF SumFunction 

=============================================================================
\* Created Thu Apr 11 10:36:10 PDT 2013 by tomr
