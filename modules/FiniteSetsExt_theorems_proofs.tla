---- MODULE FiniteSetsExt_theorems_proofs ----
EXTENDS FiniteSetsExt, Integers, FiniteSets, FiniteSetTheorems, FoldTheorems, TLAPS

(***************************************************************************)
(* Theorems about FoldSet, derived from those about the underlying         *)
(* operator MapThenFoldSet.                                                *)
(***************************************************************************)

THEOREM FoldSetEmpty ==
    ASSUME NEW op(_,_), NEW base
    PROVE  FoldSet(op, base, {}) = base
BY MapThenFoldSetEmpty, Zenon DEF FoldSet

THEOREM FoldSetNonempty ==
    ASSUME NEW op(_,_), NEW base, NEW S, S # {}, IsFiniteSet(S)
    PROVE  \E x \in S : FoldSet(op, base, S) = op(x, FoldSet(op, base, S \ {x}))
<1>1. \A T : T # {} => (CHOOSE y \in T : TRUE) \in T
  OBVIOUS
<1>. QED  BY <1>1, MapThenFoldSetNonempty, Isa DEF FoldSet

THEOREM FoldSetType ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ,
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           \A t,u \in Typ : op(t,u) \in Typ
    PROVE  FoldSet(op, base, S) \in Typ
<1>1. /\ \A T : T # {} => (CHOOSE y \in T : TRUE) \in T
      /\ \A x \in S : x \in Typ
  OBVIOUS
<1>. QED  BY <1>1, MapThenFoldSetType, Isa DEF FoldSet

THEOREM FoldSetAC ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, 
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           NEW x \in S
    PROVE  FoldSet(op, base, S) = op(x, FoldSet(op, base, S \ {x}))
<1>. /\ \A T : T # {} => (CHOOSE t \in T : TRUE) \in T 
     /\ \A s \in S : s \in Typ
  OBVIOUS
<1>. QED  BY MapThenFoldSetAC, Isa DEF FoldSet

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
<1>. /\ \A U : U # {} => (CHOOSE u \in U : TRUE) \in U 
     /\ \A x \in S \union T : x \in Typ
  OBVIOUS 
<1>. QED  BY MapThenFoldSetDisjointUnion, Isa DEF FoldSet

(***************************************************************************)
(* Theorems about SumSet.                                                  *)
(***************************************************************************)
\* we prove two type correctness theorems for Nat and for Int
THEOREM SumSetNat ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  SumSet(S) \in Nat
<1>. /\ 0 \in Nat 
     /\ \A i,j \in Nat : i+j \in Nat
  OBVIOUS
<1>. QED  BY FoldSetType, IsaM("iprover") DEF SumSet 

THEOREM SumSetInt ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  SumSet(S) \in Int
<1>. /\ 0 \in Int
     /\ \A i,j \in Int : i+j \in Int
  OBVIOUS
<1>. QED  BY FoldSetType, IsaM("iprover") DEF SumSet 

THEOREM SumSetEmpty == SumSet({}) = 0
BY FoldSetEmpty, Zenon DEF SumSet

THEOREM SumSetNonempty ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S 
    PROVE  SumSet(S) = x + SumSet(S \ {x})
<1>. DEFINE op(i,j) == i + j
<1>1. /\ 0 \in Int
      /\ \A i,j \in Int : op(i,j) \in Int
      /\ \A i,j \in Int : op(i,j) = op(j,i)
      /\ \A i,j,k \in Int : op(i, op(j,k)) = op(op(i,j), k)
  OBVIOUS
<1>. HIDE DEF op 
<1>2. FoldSet(op, 0, S) = op(x, FoldSet(op, 0, S \ {x}))
  BY <1>1, FoldSetAC, IsaM("iprover")
<1>. QED  BY <1>2 DEF SumSet, op

THEOREM SumSetDisjointUnion ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S),
           NEW T \in SUBSET Int, IsFiniteSet(T), S \cap T = {}
    PROVE  SumSet(S \union T) = SumSet(S) + SumSet(T)
<1>. DEFINE op(i,j) == i + j
<1>1. /\ 0 \in Int
      /\ \A i,j \in Int : op(i,j) \in Int
      /\ \A i,j \in Int : op(i,j) = op(j,i)
      /\ \A i,j,k \in Int : op(i, op(j,k)) = op(op(i,j), k)
      /\ \A i \in Int : op(0, i) = i
  OBVIOUS
<1>. HIDE DEF op 
<1>2. FoldSet(op, 0, S \union T) = op(FoldSet(op, 0, S), FoldSet(op, 0, T))
  BY <1>1, FoldSetDisjointUnion, IsaM("iprover")
<1>. QED   BY <1>2 DEF SumSet, op 

THEOREM SumSetNatSubset ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S),
           NEW T \in SUBSET S
    PROVE  SumSet(T) <= SumSet(S)
<1>. DEFINE U == S \ T
<1>1. /\ IsFiniteSet(T)
      /\ IsFiniteSet(U)
  BY FS_Subset, FS_Difference
<1>2. SumSet(S) = SumSet(T \union U)
  BY Zenon
<1>3. @ = SumSet(T) + SumSet(U)
  BY <1>1, SumSetDisjointUnion
<1>4. /\ SumSet(T) \in Nat 
      /\ SumSet(U) \in Nat 
  BY <1>1, SumSetNat 
<1>. QED   BY <1>2, <1>3, <1>4

THEOREM SumSetNatZero ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  SumSet(S) = 0 <=> S \subseteq {0}
<1>. DEFINE P(T) == SumSet(T) = 0 <=> T \subseteq {0}
<1>1. P({})
  BY SumSetEmpty
<1>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), P(T), NEW x \in S \ T 
      PROVE  P(T \union {x})
  <2>1. /\ IsFiniteSet(T \union {x})
        /\ T \union {x} \in SUBSET Nat
        /\ x \in T \union {x}
        /\ (T \union {x}) \ {x} = T
    BY <1>2, FS_AddElement
  <2>2. SumSet(T \union {x}) = x + SumSet(T)
    BY ONLY <2>1, SumSetNonempty
  <2>3. SumSet(T) \in Nat 
    BY <1>2, SumSetNat
  <2>4. SumSet(T \union {x}) = 0 <=> x = 0 /\ SumSet(T) = 0
    BY <2>2, <2>3
  <2>. QED  BY <1>2, <2>4
<1>. QED
  <2>. HIDE DEF P 
  <2>. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("iprover")
  <2>. QED   BY DEF P

(***************************************************************************)
(* Theorems about ProductSet.                                              *)
(***************************************************************************)
THEOREM ProductSetNat ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  ProductSet(S) \in Nat
<1>. /\ 1 \in Nat 
     /\ \A i,j \in Nat : i*j \in Nat
  OBVIOUS
<1>. QED  BY FoldSetType, IsaM("iprover") DEF ProductSet 

THEOREM ProductSetInt ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  ProductSet(S) \in Int
<1>. /\ 1 \in Int
     /\ \A i,j \in Int : i*j \in Int
  OBVIOUS
<1>. QED  BY FoldSetType, IsaM("iprover") DEF ProductSet 

THEOREM ProductSetEmpty == ProductSet({}) = 1
BY FoldSetEmpty, Zenon DEF ProductSet

THEOREM ProductSetNonempty ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S 
    PROVE  ProductSet(S) = x * ProductSet(S \ {x})
<1>. DEFINE op(i,j) == i * j
<1>1. /\ 1 \in Int
      /\ \A i,j \in Int : op(i,j) \in Int
      /\ \A i,j \in Int : op(i,j) = op(j,i)
      /\ \A i,j,k \in Int : op(i, op(j,k)) = op(op(i,j), k)
  OBVIOUS
<1>. HIDE DEF op 
<1>2. FoldSet(op, 1, S) = op(x, FoldSet(op, 1, S \ {x}))
  BY <1>1, FoldSetAC, IsaM("iprover")
<1>. QED  BY <1>2 DEF ProductSet, op

THEOREM ProductSetDisjointUnion ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S),
           NEW T \in SUBSET Int, IsFiniteSet(T), S \cap T = {}
    PROVE  ProductSet(S \union T) = ProductSet(S) * ProductSet(T)
<1>. DEFINE op(i,j) == i * j
<1>1. /\ 1 \in Int
      /\ \A i,j \in Int : op(i,j) \in Int
      /\ \A i,j \in Int : op(i,j) = op(j,i)
      /\ \A i,j,k \in Int : op(i, op(j,k)) = op(op(i,j), k)
      /\ \A i \in Int : op(1, i) = i
  OBVIOUS
<1>. HIDE DEF op 
<1>2. FoldSet(op, 1, S \union T) = op(FoldSet(op, 1, S), FoldSet(op, 1, T))
  BY <1>1, FoldSetDisjointUnion, IsaM("iprover")
<1>. QED   BY <1>2 DEF ProductSet, op 

THEOREM ProductSetNatOne ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S)
    PROVE  ProductSet(S) = 1 <=> S \subseteq {1}
<1>. DEFINE P(T) == ProductSet(T) = 1 <=> T \subseteq {1}
<1>1. P({})
  BY ProductSetEmpty
<1>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), P(T), NEW x \in S \ T 
      PROVE  P(T \union {x})
  <2>1. /\ IsFiniteSet(T \union {x})
        /\ T \union {x} \in SUBSET Nat
        /\ x \in T \union {x}
        /\ (T \union {x}) \ {x} = T
    BY <1>2, FS_AddElement
  <2>2. ProductSet(T \union {x}) = x * ProductSet(T)
    BY ONLY <2>1, ProductSetNonempty
  <2>3. ProductSet(T) \in Nat 
    BY <1>2, ProductSetNat
  <2>4. ProductSet(T \union {x}) = 1 <=> x = 1 /\ ProductSet(T) = 1
    BY <2>2, <2>3
  <2>. QED  BY <1>2, <2>4
<1>. QED
  <2>. HIDE DEF P 
  <2>. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("iprover")
  <2>. QED   BY DEF P

THEOREM ProductSetZero ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S)
    PROVE  ProductSet(S) = 0 <=> 0 \in S 
<1>. DEFINE P(T) == ProductSet(T) = 0 <=> 0 \in T 
<1>1. P({})
  BY ProductSetEmpty
<1>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), P(T), NEW x \in S \ T 
      PROVE  P(T \union {x})
  <2>1. /\ IsFiniteSet(T \union {x})
        /\ T \union {x} \in SUBSET Int
        /\ x \in T \union {x}
        /\ (T \union {x}) \ {x} = T
    BY <1>2, FS_AddElement
  <2>2. ProductSet(T \union {x}) = x * ProductSet(T)
    BY ONLY <2>1, ProductSetNonempty
  <2>3. ProductSet(T) \in Int
    BY <1>2, ProductSetInt
  <2>4. ProductSet(T \union {x}) = 0 <=> x = 0 \/ ProductSet(T) = 0
    BY <2>2, <2>3
  <2>. QED  BY <1>2, <2>4
<1>. QED
  <2>. HIDE DEF P 
  <2>. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("iprover")
  <2>. QED   BY DEF P

THEOREM ProductSetNatSubset ==
    ASSUME NEW S \in SUBSET Nat, IsFiniteSet(S), 0 \notin S,
           NEW T \in SUBSET S
    PROVE  ProductSet(T) <= ProductSet(S)
<1>. DEFINE U == S \ T
<1>1. /\ IsFiniteSet(T)
      /\ IsFiniteSet(U)
  BY FS_Subset, FS_Difference
<1>2. ProductSet(S) = ProductSet(T \union U)
  BY Zenon
<1>3. @ = ProductSet(T) * ProductSet(U)
  BY <1>1, ProductSetDisjointUnion
<1>4. /\ ProductSet(T) \in Nat 
      /\ ProductSet(U) \in Nat 
  BY <1>1, ProductSetNat 
<1>5. /\ ProductSet(T) # 0
      /\ ProductSet(U) # 0 
  BY <1>1, ProductSetZero
<1>. QED   BY <1>2, <1>3, <1>4, <1>5


(***************************************************************************)
(* Theorems about MapThenSumSet.                                           *)
(***************************************************************************)
THEOREM MapThenSumSetNat ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Nat
    PROVE  MapThenSumSet(op, S) \in Nat
<1>. \A T \in SUBSET S : T # {} => (CHOOSE x \in T : TRUE) \in T 
  OBVIOUS
<1>. /\ 0 \in Nat
     /\ \A i,j \in Nat : i+j \in Nat 
  OBVIOUS
<1>. QED  BY MapThenFoldSetType, IsaM("iprover") DEF MapThenSumSet

THEOREM MapThenSumSetInt ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Int
    PROVE  MapThenSumSet(op, S) \in Int
<1>. \A T \in SUBSET S : T # {} => (CHOOSE x \in T : TRUE) \in T 
  OBVIOUS
<1>. /\ 0 \in Int
     /\ \A i,j \in Int : i+j \in Int
  OBVIOUS
<1>. QED  BY MapThenFoldSetType, IsaM("iprover") DEF MapThenSumSet

THEOREM MapThenSumSetEmpty == 
    ASSUME NEW op(_)
    PROVE  MapThenSumSet(op, {}) = 0
BY MapThenFoldSetEmpty, Zenon DEF MapThenSumSet 

THEOREM MapThenSumSetNonempty ==
    ASSUME NEW S, IsFiniteSet(S), NEW x \in S,
           NEW op(_), \A s \in S : op(s) \in Int
    PROVE  MapThenSumSet(op, S) = op(x) + MapThenSumSet(op, S \ {x})
<1>. \A T \in SUBSET S : T # {} => (CHOOSE t \in T : TRUE) \in T 
  OBVIOUS
<1>. /\ 0 \in Int 
     /\ \A i,j \in Int : i+j \in Int
     /\ \A i,j \in Int : i+j = j+i 
     /\ \A i,j,k \in Int : i+(j+k) = (i+j)+k
  OBVIOUS
<1>. QED  BY MapThenFoldSetAC, IsaM("iprover") DEF MapThenSumSet 

THEOREM MapThenSumSetDisjointUnion ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW T, IsFiniteSet(T), S \cap T = {},
           NEW op(_), \A x \in S \union T : op(x) \in Int
    PROVE  MapThenSumSet(op, S \union T) = 
           MapThenSumSet(op, S) + MapThenSumSet(op, T)
<1>1. \A U \in SUBSET (S \union T) : U # {} => (CHOOSE u \in U : TRUE) \in U 
  OBVIOUS
<1>2. /\ 0 \in Int 
      /\ \A i,j \in Int : i+j \in Int
      /\ \A i,j \in Int : i+j = j+i
      /\ \A i,j,k \in Int : i+(j+k) = (i+j)+k
      /\ \A i \in Int : 0+i = i
  OBVIOUS
<1>. QED  BY <1>1, <1>2, MapThenFoldSetDisjointUnion, IsaM("iprover") DEF MapThenSumSet 

THEOREM MapThenSumSetNatSubset ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW T \in SUBSET S,
           NEW op(_), \A x \in S : op(x) \in Nat
    PROVE  MapThenSumSet(op, T) <= MapThenSumSet(op, S)
<1>. DEFINE U == S \ T
<1>1. /\ IsFiniteSet(T)
      /\ IsFiniteSet(U)
      /\ T \cap U = {}
      /\ \A x \in T \union U : op(x) \in Int
  BY FS_Subset, FS_Difference
<1>2. MapThenSumSet(op, S) = MapThenSumSet(op, T \union U)
  BY Zenon
<1>3. @ = MapThenSumSet(op, T) + MapThenSumSet(op, U)
  BY <1>1, MapThenSumSetDisjointUnion, IsaM("iprover")
<1>4. /\ \A x \in T : op(x) \in Nat 
      /\ \A x \in U : op(x) \in Nat 
  OBVIOUS
<1>5. /\ MapThenSumSet(op, T) \in Nat 
      /\ MapThenSumSet(op, U) \in Nat 
  BY <1>1, <1>4, MapThenSumSetNat, IsaM("iprover")
<1>. QED   BY <1>2, <1>3, <1>5

THEOREM MapThenSumSetZero ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A s \in S : op(s) \in Nat 
    PROVE  MapThenSumSet(op, S) = 0 <=> \A s \in S : op(s) = 0
<1>. DEFINE P(T) == MapThenSumSet(op, T) = 0 <=> \A s \in T : op(s) = 0
<1>1. P({})
  BY MapThenSumSetEmpty, Zenon
<1>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), P(T), NEW x \in S \ T 
      PROVE  P(T \union {x})
  <2>1. /\ IsFiniteSet(T \union {x})
        /\ \A s \in T \union {x} : op(s) \in Int
    BY <1>2, FS_AddElement
  <2>2. MapThenSumSet(op, T \union {x}) = op(x) + MapThenSumSet(op, (T \union {x}) \ {x})
    BY ONLY <2>1, MapThenSumSetNonempty, IsaM("blast")
  <2>3. @ = op(x) + MapThenSumSet(op, T)
    BY Zenon
  <2>4. MapThenSumSet(op, T) \in Nat 
    BY <1>2, \A s \in T : op(s) \in Nat, MapThenSumSetNat, IsaM("iprover")
  <2>5. MapThenSumSet(op, T \union {x}) = 0 <=> op(x) = 0 /\ MapThenSumSet(op, T) = 0
    BY <2>2, <2>3, <2>4
  <2>. QED  BY <1>2, <2>5
<1>. QED 
  <2>. HIDE DEF P 
  <2>. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("iprover")
  <2>. QED   BY DEF P

THEOREM MapThenSumSetMonotonic ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), \A s \in S : f(s) \in Int,
           NEW g(_), \A s \in S : g(s) \in Int,
           \A s \in S : f(s) <= g(s)
    PROVE  MapThenSumSet(f, S) <= MapThenSumSet(g, S)
<1>. DEFINE P(T) == MapThenSumSet(f, T) <= MapThenSumSet(g, T)
<1>1. P({})
  BY MapThenSumSetEmpty, Isa
<1>2. ASSUME NEW T \in SUBSET S, IsFiniteSet(T), P(T), NEW x \in S \ T 
      PROVE  P(T \union {x})
  <2>1. /\ IsFiniteSet(T \union {x})
        /\ \A s \in T \union {x} : f(s) \in Int
        /\ \A s \in T \union {x} : g(s) \in Int
\*        /\ \A s \in T \union {x} : f(s) <= g(s)
    BY <1>2, FS_AddElement
  <2>2. MapThenSumSet(f, T \union {x}) = f(x) + MapThenSumSet(f, (T \union {x}) \ {x})
    BY ONLY <2>1, MapThenSumSetNonempty, IsaM("blast")
  <2>3. @ = f(x) + MapThenSumSet(f, T)
    BY Zenon
  <2>4. MapThenSumSet(f, T) \in Int
    BY <1>2, \A s \in T : f(s) \in Int, MapThenSumSetInt, IsaM("iprover")
  <2>5. MapThenSumSet(g, T \union {x}) = g(x) + MapThenSumSet(g, (T \union {x}) \ {x})
    BY ONLY <2>1, MapThenSumSetNonempty, IsaM("blast")
  <2>6. @ = g(x) + MapThenSumSet(g, T)
    BY Zenon
  <2>7. MapThenSumSet(g, T) \in Int
    BY <1>2, \A s \in T : g(s) \in Int, MapThenSumSetInt, IsaM("iprover")
  <2>. QED  BY <1>2, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7
<1>. QED 
  <2>. HIDE DEF P 
  <2>. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("iprover")
  <2>. QED   BY DEF P

THEOREM MapThenSumSetStrictlyMonotonic ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW f(_), \A s \in S : f(s) \in Int,
           NEW g(_), \A s \in S : g(s) \in Int,
           \A s \in S : f(s) <= g(s),
           \E s \in S : f(s) < g(s)
    PROVE  MapThenSumSet(f, S) < MapThenSumSet(g, S)
<1>1. PICK s \in S : f(s) < g(s)
  OBVIOUS 
<1>2. MapThenSumSet(f,S) = f(s) + MapThenSumSet(f, S \ {s})
  BY MapThenSumSetNonempty, Isa
<1>3. MapThenSumSet(g,S) = g(s) + MapThenSumSet(g, S \ {s})
  BY MapThenSumSetNonempty, Isa
<1>4. /\ IsFiniteSet(S \ {s})
      /\ \A x \in S \ {s} : f(x) \in Int 
      /\ \A x \in S \ {s} : g(x) \in Int 
      /\ \A x \in S \ {s} : f(x) <= g(x)
  BY FS_RemoveElement
<1>5. MapThenSumSet(f, S \ {s}) <= MapThenSumSet(g, S \ {s})
  BY <1>4, MapThenSumSetMonotonic, IsaM("blast")
<1>6. /\ MapThenSumSet(f, S \ {s}) \in Int 
      /\ MapThenSumSet(g, S \ {s}) \in Int 
  BY <1>4, MapThenSumSetInt, Isa
<1>. QED  BY <1>1, <1>2, <1>3, <1>5, <1>6


================================================================================

\* old proofs specifically about MapThenSumSet via an auxiliary operator
--------------------------------------------------------------------------------
(***************************************************************************)
(* NatAsSet represents a number N as a set of size S. The tag argument     *)
(* can be used to make such sets additive by selecting unique tags.        *)
(***************************************************************************)

NatAsSet(tag, n) == { <<tag, i>> : i \in 1..n }


LEMMA NatAsSetProps ==
    ASSUME NEW tag, NEW e \in Nat
    PROVE  IsFiniteSet(NatAsSet(tag, e)) /\ Cardinality(NatAsSet(tag, e)) = e
PROOF
    <1> USE DEF NatAsSet
    <1> DEFINE P(n) == IsFiniteSet(NatAsSet(tag, n)) /\ Cardinality(NatAsSet(tag, n)) = n
    <1>3. \A n \in Nat : P(n)
        <2>1. P(0) BY FS_EmptySet
        <2>2. \A n \in Nat : P(n) => P(n+1)
            <3> SUFFICES ASSUME NEW n \in Nat, P(n) PROVE P(n+1) OBVIOUS
            <3>2. NatAsSet(tag, n+1) = NatAsSet(tag, n) \cup {<<tag, n+1>>} OBVIOUS
            <3>3. <<tag, n+1>> \notin NatAsSet(tag, n) OBVIOUS
            <3>4. IsFiniteSet(NatAsSet(tag, n+1)) BY <3>2, FS_AddElement
            <3>5. Cardinality(NatAsSet(tag, n+1)) = Cardinality(NatAsSet(tag, n)) + 1 BY FS_AddElement, <3>2, <3>3, <3>4
            <3>q. QED BY <3>4, <3>5
        <2> HIDE DEF P
        <2>q. QED BY NatInduction, <2>1, <2>2
    <1>q. QED BY <1>3 DEF P


LEMMA NatAsSetTagsPartition ==
    ASSUME NEW t1, NEW t2, NEW n1 \in Nat, NEW n2 \in Nat, t1 # t2
    PROVE  NatAsSet(t1, n1) \cap NatAsSet(t2, n2) = {}
PROOF
    BY DEF NatAsSet


LEMMA NatAsSetCardAdd ==
    ASSUME NEW t1, NEW t2, NEW n1 \in Nat, NEW n2 \in Nat, t1 # t2
    PROVE Cardinality(NatAsSet(t1, n1) \cup NatAsSet(t2, n2)) = Cardinality(NatAsSet(t1, n1)) + Cardinality(NatAsSet(t2, n2))
PROOF
    <1>1. IsFiniteSet(NatAsSet(t1, n1)) /\ IsFiniteSet(NatAsSet(t2, n2)) BY NatAsSetProps
    <1>2. Cardinality(NatAsSet(t1, n1) \cap NatAsSet(t2, n2)) = 0 BY NatAsSetTagsPartition, FS_EmptySet
    <1>3. Cardinality(NatAsSet(t1, n1)) = n1 BY NatAsSetProps
    <1>4. Cardinality(NatAsSet(t2, n2)) = n2 BY NatAsSetProps
    <1>5. Cardinality(NatAsSet(t1, n1) \cup NatAsSet(t2, n2)) = n1 + n2 BY FS_Union, FS_EmptySet, <1>1, <1>2, <1>3, <1>4
    <1>q. QED BY <1>3, <1>4, <1>5


--------------------------------------------------------------------------------
(***************************************************************************)
(* A sum of set S is expressed as a cardinality of a set constructed by    *)
(* taking union of sets representing the elements S.                       *)
(***************************************************************************)

CardSum(S, op(_)) == Cardinality(UNION { NatAsSet(n, op(n)) : n \in S })


LEMMA CardSumEmpty ==
    ASSUME NEW op(_)
    PROVE CardSum({}, op) = 0
PROOF
    BY FS_EmptySet, FS_UNION DEF CardSum


LEMMA CardSumType ==
    ASSUME NEW S, IsFiniteSet(S), NEW op(_), \A e \in S : op(e) \in Nat
    PROVE CardSum(S, op) \in Nat
PROOF
    <1>1. \A e \in S : op(e) \in Nat OBVIOUS
    <1>a. IsFiniteSet({ NatAsSet(e, op(e)) : e \in S }) BY FS_Image
    <1>2. \A e \in S : IsFiniteSet(NatAsSet(e, op(e))) BY NatAsSetProps, <1>1
    <1>3. IsFiniteSet(UNION { NatAsSet(e, op(e)) : e \in S }) BY FS_UNION, <1>2, <1>a
    <1>q. QED BY <1>3, FS_CardinalityType DEF CardSum


LEMMA CardSumAddElem ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e, e \notin S, op(e) \in Nat
    PROVE CardSum(S \cup {e}, op) = CardSum(S, op) + op(e)
PROOF
    <1> DEFINE old == UNION { NatAsSet(s, op(s)) : s \in S }
    <1> DEFINE new == NatAsSet(e, op(e))
    <1> DEFINE all == UNION { NatAsSet(s, op(s)) : s \in S \cup {e} }
    <1>1. all = old \cup new OBVIOUS
    <1>2. IsFiniteSet(old)
        <2>1. \A s \in S : IsFiniteSet(NatAsSet(s, op(s))) BY NatAsSetProps
        <2>q. QED BY <2>1, FS_UNION, FS_Image
    <1>3. IsFiniteSet(new) BY NatAsSetProps
    <1>4. Cardinality(old) = CardSum(S, op) BY DEF CardSum
    <1>5. Cardinality(new) = op(e) BY NatAsSetProps
    <1>6. Cardinality(old \cap new) = 0
        <2>1. \A s \in S : NatAsSet(s, op(s)) \cap NatAsSet(e, op(e)) = {} BY NatAsSetTagsPartition
        <2>2. old \cap new = {} BY <2>1
        <2>q. QED BY <2>2, FS_EmptySet
    <1>q. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, FS_Union DEF CardSum

LEMMA CardSumAddElemSym ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e, e \notin S, op(e) \in Nat
    PROVE CardSum(S \cup {e}, op) = op(e) + CardSum(S, op)
PROOF
    <1> DEFINE a == CardSum(S \cup {e}, op)
               b == CardSum(S, op)
               c == op(e)
    <1> HIDE DEF a, b, c
    <1>1. a = b + c BY CardSumAddElem DEF a, b, c
    <1>3. b \in Nat BY CardSumType DEF b
    <1>4. c \in Nat BY DEF c
    <1>5. b + c = c + b BY <1>3, <1>4
    <1>6. a = c + b BY <1>1, <1>5
    <1>q. QED BY <1>6 DEF a, b, c


LEMMA CardSumRemElem ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e \in S
    PROVE CardSum(S, op) = CardSum(S \ {e}, op) + op(e)
PROOF
    <1> DEFINE T == S \ {e}
    <1>1. IsFiniteSet(T) BY FS_Difference, FS_Singleton
    <1>2. e \notin T OBVIOUS
    <1>3. op(e) \in Nat OBVIOUS
    <1>4. \A s \in T : op(s) \in Nat OBVIOUS
    <1>9. CardSum(T \cup {e}, op) = CardSum(T, op) + op(e)
        BY <1>1, <1>2, <1>3, <1>4, CardSumAddElem
    <1>q. QED BY <1>9 DEF T

LEMMA CardSumRemElemSym ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e \in S
    PROVE CardSum(S, op) = op(e) + CardSum(S \ {e}, op)
PROOF
    <1> DEFINE a == CardSum(S, op)
               b == CardSum(S \ {e}, op)
               c == op(e)
    <1> HIDE DEF a, b, c
    <1>1. a = b + c BY CardSumRemElem DEF a, b, c
    <1>3. b \in Nat
        <2>1. \A x \in S \ {e} : op(x) \in Nat OBVIOUS
        <2>q. QED BY <2>1, CardSumType, FS_Difference DEF b
    <1>4. c \in Nat BY DEF c
    <1>5. b + c = c + b BY <1>3, <1>4
    <1>6. a = c + b BY <1>1, <1>5
    <1>q. QED BY <1>6 DEF a, b, c


LEMMA CardSumMonotonic ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e, e \notin S, op(e) \in Nat
    PROVE CardSum(S \cup {e}, op) >= CardSum(S, op)
    <1>1. CardSum(S \cup {e}, op) = CardSum(S, op) + op(e) BY CardSumAddElem
    <1>2. op(e) >= 0 OBVIOUS
    <1>q. QED BY <1>1, <1>2, CardSumType


LEMMA CardSumMonotonicOpGE ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op1(_), \A s \in S : op1(s) \in Nat,
        NEW op2(_), \A s \in S : op2(s) \in Nat,
        \A s \in S : op2(s) >= op1(s)
    PROVE
        CardSum(S, op2) >= CardSum(S, op1)
PROOF
    <1> DEFINE P(s) == s \subseteq S => CardSum(s, op2) >= CardSum(s, op1)
    <1> HIDE DEF P
    <1> SUFFICES P(S) BY DEF P
    <1>1. IsFiniteSet(S) OBVIOUS
    <1>2. P({}) BY CardSumEmpty, Isa DEF P
    <1>3. ASSUME
            NEW CONSTANT T,
            NEW CONSTANT x,
            IsFiniteSet(T) ,
            P(T) ,
            x \notin T
        PROVE P(T \cup {x})
        <2> SUFFICES ASSUME
                T \cup {x} \subseteq S
            PROVE CardSum(T \cup {x}, op2) >= CardSum(T \cup {x}, op1)
            BY DEF P
        <2>2. \A s \in T : op1(s) \in Nat OBVIOUS
        <2>3. \A s \in T : op2(s) \in Nat OBVIOUS
        <2>4. op1(x) \in Nat OBVIOUS
        <2>5. op2(x) \in Nat OBVIOUS
        <2>6. CardSum(T \cup {x}, op1) = CardSum(T, op1) + op1(x) BY ONLY <1>3, <2>2, <2>4, CardSumAddElem, Isa
        <2>7. CardSum(T \cup {x}, op2) = CardSum(T, op2) + op2(x) BY ONLY <1>3, <2>3, <2>5, CardSumAddElem, Isa
        <2>8. CardSum(T, op2) >= CardSum(T, op1) BY <1>3 DEF P
        <2>9. op2(x) >= op1(x) BY <1>3
        <2>10. CardSum(T, op1) \in Nat BY CardSumType, <1>3, <2>2
        <2>11. CardSum(T, op2) \in Nat BY CardSumType, <1>3, <2>3
        <2>q. QED BY <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11
    <1>q. QED BY ONLY FS_Induction, <1>1, <1>2, <1>3, Isa


LEMMA CardSumMonotonicOpGT ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op1(_), \A s \in S : op1(s) \in Nat,
        NEW op2(_), \A s \in S : op2(s) \in Nat,
        \A s \in S : op2(s) >= op1(s),
        \E s \in S : op2(s) > op1(s)
    PROVE
        CardSum(S, op2) > CardSum(S, op1)
PROOF
    <1>1. PICK x \in S : op2(x) > op1(x) OBVIOUS
    <1> DEFINE T == S \ {x}
    <1> HIDE DEF T
    <1>2. S = T \cup {x} BY <1>1 DEF T
    <1>3. IsFiniteSet(T) BY FS_Singleton, FS_Difference DEF T
    <1>4. \A t \in T : op1(t) \in Nat BY DEF T
    <1>5. \A t \in T : op2(t) \in Nat BY DEF T
    <1>6. CardSum(T, op2) >= CardSum(T, op1)
        <2>4. \A t \in T : op2(t) >= op1(t) BY DEF T
        <2>q. QED BY ONLY CardSumMonotonicOpGE, <1>3, <1>4, <1>5, <2>4, Isa
    <1>7. op1(x) \in Nat OBVIOUS
    <1>8. op2(x) \in Nat OBVIOUS
    <1>9. x \notin T BY DEF T
    <1>10. CardSum(T \cup {x}, op1) = CardSum(T, op1) + op1(x) BY ONLY <1>3, <1>4, <1>9, <1>7, CardSumAddElem, Isa
    <1>11. CardSum(T \cup {x}, op2) = CardSum(T, op2) + op2(x) BY ONLY <1>3, <1>5, <1>9, <1>8, CardSumAddElem, Isa
    <1>12. op2(x) > op1(x) BY <1>1
    <1>13. CardSum(T, op1) \in Nat BY CardSumType, <1>3, <1>4
    <1>14. CardSum(T, op2) \in Nat BY CardSumType, <1>3, <1>5
    <1>q. QED BY <1>1, <1>2, <1>6, <1>7, <1>8, <1>10, <1>11, <1>12, <1>13, <1>14


LEMMA CardSumZero ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A e \in S: op(e) \in Nat,
           CardSum(S, op) = 0
    PROVE \A e \in S: op(e) = 0
PROOF
    <1> SUFFICES ASSUME NEW e \in S PROVE op(e) = 0 OBVIOUS
    <1> DEFINE T == S \ {e}
    <1>1. e \notin T OBVIOUS
    <1>2. op(e) \in Nat OBVIOUS
    <1>3. S = T \cup {e} OBVIOUS
    <1>4. IsFiniteSet(T) BY FS_Difference, FS_Singleton
    <1>5. \A s \in T : op(s) \in Nat OBVIOUS
    <1>a. CardSum(T, op) \in Nat BY CardSumType, <1>2, <1>4, <1>5
    <1>6. CardSum(S, op) = CardSum(T, op) + op(e) BY CardSumRemElem
    <1>7. CardSum(S, op) = 0 OBVIOUS
    <1> HIDE DEF T
    <1>8. CardSum(S, op) >= CardSum(T, op)
        <2> SUFFICES ASSUME TRUE PROVE CardSum(T \cup {e}, op) >= CardSum(T, op) BY DEF T
        <2>q. QED BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, CardSumMonotonic
    <1>9. CardSum(T, op) = 0 BY <1>7, <1>8, <1>a
    <1>q. QED BY <1>7, <1>9, <1>a, <1>2, <1>6

LEMMA CardSumZeros ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A e \in S: op(e) = 0
    PROVE CardSum(S, op) = 0
PROOF
    <1> DEFINE P(s) == s \subseteq S => CardSum(s, op) = 0
    <1> HIDE DEF P
    <1>0. IsFiniteSet(S) OBVIOUS
    <1>1. P({}) BY CardSumEmpty DEF P
    <1>2. ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T PROVE P(T \cup {x})
        <2> SUFFICES ASSUME T \subseteq S, x \in S PROVE P(T \cup {x}) BY DEF P
        <2>1. CardSum(T, op) = 0 BY <1>2 DEF P
        <2>2. T \cup {x} \subseteq S OBVIOUS
        <2>3. CardSum(T \cup {x}, op) = CardSum(T, op) + op(x)
            <3> IsFiniteSet(T) BY FS_Subset
            <3> \A s \in T : op(s) \in Nat OBVIOUS
            <3> x \notin T BY <1>2
            <3> op(x) \in Nat OBVIOUS
            <3>q. QED BY CardSumAddElem
        <2>4. op(x) = 0 OBVIOUS
        <2>5. CardSum(T \cup {x}, op) = 0
            <3>1. IsFiniteSet(T \cup {x}) BY <1>2, FS_Union, FS_Singleton
            <3>2. \A s \in T \cup {x} : op(s) \in Nat OBVIOUS
            <3>4. CardSum(T \cup {x}, op) \in Nat BY <3>1, <3>2, CardSumType
            <3> QED BY ONLY <2>1, <2>3, <2>4, <3>4
        <2>q. QED BY <2>5 DEF P
    <1>3. P(S) BY ONLY <1>0, <1>1, <1>2, FS_Induction
    <1>q. QED BY <1>3 DEF P

--------------------------------------------------------------------------------

(*
This lemma is used later to transfer the results on CardSum to MapThenSumSet.
The proof follows closely lemma FS_CountingElements from FiniteSetTheorems_proofs.tla
*)
LEMMA MapThenSumSetDefined ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat
    PROVE MapThenSumSet(op, S) = CardSum(S, op)
PROOF
    (* "Simple Function" *)
    <1> DEFINE CardSumF == [s \in SUBSET S |-> CardSum(s, op)]

    (* Function part of the IsF. *)
    <1> DEFINE fn(F, s) ==
        IF s = {}
        THEN 0
        ELSE LET e == CHOOSE e \in s : TRUE IN op(e) + F[s \ {e}]

    <1> DEFINE IsF(F) == F = [s \in SUBSET S |-> fn(F, s)]

    <1> F == CHOOSE F : IsF(F)

    <1> HIDE DEF CardSumF, F, fn
    <1>1. IsF(CardSumF)
        <2> DEFINE P(s) == \A ss \in SUBSET s : ss \in SUBSET S => CardSumF[ss] = fn(CardSumF,ss)
        <2> HIDE DEF P
        <2>0. IsFiniteSet(S) OBVIOUS
        <2>1. P({}) BY CardSumEmpty DEF P, CardSumF, fn
        <2>2. ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T PROVE P(T \cup {x})
            <3> DEFINE Tx == T \cup {x}
            <3> HIDE DEF Tx
            <3>0. IsFiniteSet(Tx) BY <2>2, FS_AddElement DEF Tx
            <3>1. \A t \in SUBSET Tx :
                    \/ t \in SUBSET T
                    \/ \E tt \in SUBSET T : t = tt \cup {x}
                  BY DEF Tx
            <3>2. SUFFICES ASSUME NEW tx \in SUBSET Tx
                  PROVE tx \in SUBSET S => CardSumF[tx] = fn(CardSumF, tx) BY DEF P, Tx
            <3>3. CASE tx \in SUBSET T BY <3>3, <2>2 DEF P
            <3>4. CASE \E tt \in SUBSET T : tx = tt \cup {x}
                <4>0. tx # {} /\ \E e \in tx : TRUE BY <3>4
                <4>1. SUFFICES ASSUME tx \in SUBSET S
                      PROVE CardSum(tx, op) = fn(CardSumF, tx) BY DEF CardSumF
                <4>d. SUFFICES ASSUME TRUE
                      PROVE CardSum(tx, op) = (LET e == CHOOSE e \in tx : TRUE IN op(e) + CardSumF[tx \ {e}])
                      BY <4>0 DEF fn
                <4>e. SUFFICES ASSUME NEW txe \in tx
                      PROVE CardSum(tx, op) = op(txe) + CardSumF[tx \ {txe}]
                      BY <4>0
                <4>g. tx \ {txe} \in SUBSET S BY <4>1
                <4>f. SUFFICES ASSUME TRUE
                      PROVE CardSum(tx, op) = op(txe) + CardSum(tx \ {txe}, op)
                      BY <4>g DEF CardSumF
                <4>h. IsFiniteSet(tx) BY <3>0, <3>2, FS_Subset
                <4>i. \A t \in tx : op(t) \in Nat BY <4>1
                <4>j. txe \in tx BY <4>e
                <4>q. QED BY CardSumRemElemSym, <4>h, <4>i, <4>j
            <3>q. QED BY <3>3, <3>4, <3>1
        <2>3. P(S) BY ONLY <2>0, <2>1, <2>2, FS_Induction
        <2>q. QED BY <2>3 DEF P, IsF, CardSumF
    <1>2. ASSUME NEW F1, IsF(F1),
                 NEW F2, IsF(F2)
          PROVE F1 = F2
        <2> DEFINE P(i) == \A T \in SUBSET S : Cardinality(T) = i => F1[T] = F2[T]
        <2> HIDE DEF P
        <2>0. \A ss \in SUBSET S :
                /\ F1[ss] = fn(F1, ss)
                /\ F2[ss] = fn(F2, ss)
              BY <1>2 DEF IsF
        <2>1. \A i \in Nat : P(i)
            <3>1. P(0)
                <4> SUFFICES ASSUME NEW T \in SUBSET S, Cardinality(T) = 0
                    PROVE F1[T] = F2[T]
                    BY DEF P
                <4>2. T = {} BY FS_EmptySet, FS_Subset
                <4>q. QED BY <2>0, <4>2 DEF fn
            <3>2. \A n \in Nat : P(n) => P(n+1)
                <4> SUFFICES ASSUME NEW n \in Nat, P(n) PROVE P(n+1) OBVIOUS
                <4> SUFFICES ASSUME NEW Tx \in SUBSET S, Cardinality(Tx) = n + 1 PROVE F1[Tx] = F2[Tx] BY DEF P
                <4>0. IsFiniteSet(Tx) BY FS_Subset
                <4>1. Tx # {} BY FS_EmptySet
                <4>2. PICK x \in Tx : x = CHOOSE xx \in Tx : TRUE BY <4>1
                <4> DEFINE T == Tx \ {x}
                <4>3. IsFiniteSet(T) BY <4>0, FS_Difference
                <4>4. Cardinality(T) = n
                    <5>1. Tx \cap {x} = {x} BY <4>2
                    <5>2. Cardinality(Tx \cap {x}) = 1 BY <5>1, FS_Singleton
                    <5>q. QED BY <4>0, <5>2, FS_Difference
                <4>5. F1[T] = F2[T] BY <4>4 DEF P
                <4>6. F1[Tx] = op(x) + F1[T] BY <2>0, <4>2 DEF P, fn
                <4>7. F2[Tx] = op(x) + F2[T] BY <2>0, <4>2 DEF P, fn
                <4>q. QED BY <4>5, <4>6, <4>7 DEF P
            <3>q. QED BY <3>1, <3>2, NatInduction
        <2>2. SUFFICES ASSUME NEW T \in SUBSET S PROVE F1[T] = F2[T] BY <1>2
        <2>3. \E i \in Nat : Cardinality(T) = i BY FS_CardinalityType, FS_Subset
        <2>q. QED BY <2>1, <2>3 DEF P
    <1>3. IsF(F) BY <1>1 DEF F
    <1>4. F = CardSumF BY <1>1, <1>2, <1>3
    <1>q. QED BY <1>4 DEF MapThenSumSet, MapThenFoldSet, CardSum, CardSumF, F, fn


--------------------------------------------------------------------------------
\* And finally, transfer the CardSum theorems to MapThenSumSet.

LEMMA MapThenSumSetEmpty ==
    ASSUME NEW op(_)
    PROVE MapThenSumSet(op, {}) = 0
PROOF
    BY CardSumEmpty, MapThenSumSetDefined, FS_EmptySet


LEMMA MapThenSumSetType ==
    ASSUME NEW S, IsFiniteSet(S), NEW op(_), \A e \in S : op(e) \in Nat
    PROVE MapThenSumSet(op, S) \in Nat
PROOF
    BY CardSumType, MapThenSumSetDefined


THEOREM MapThenSumSetAddElem ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e, e \notin S, op(e) \in Nat
    PROVE MapThenSumSet(op, S \cup {e}) = MapThenSumSet(op, S) + op(e)
PROOF
    <1>0. IsFiniteSet(S \cup {e}) BY FS_Union, FS_Singleton
    <1>1. CardSum(S \cup {e}, op) = CardSum(S, op) + op(e) BY CardSumAddElem
    <1>2. CardSum(S \cup {e}, op) = MapThenSumSet(op, S \cup {e}) BY MapThenSumSetDefined, <1>0
    <1>3. MapThenSumSet(op, S) = CardSum(S, op) BY MapThenSumSetDefined
    <1>q. QED BY <1>1, <1>2, <1>3

LEMMA MapThenSumSetRemElem ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e \in S
    PROVE MapThenSumSet(op, S) = MapThenSumSet(op, S \ {e}) + op(e)
PROOF
    <1>1. IsFiniteSet(S \ {e}) BY FS_Difference, FS_Singleton
    <1>2. MapThenSumSet(op, S) = CardSum(S, op) BY MapThenSumSetDefined
    <1>3. MapThenSumSet(op, S \ {e}) = CardSum(S \ {e}, op) BY MapThenSumSetDefined, <1>1
    <1>q. QED BY <1>2, <1>3, CardSumRemElem

LEMMA MapThenSumSetMonotonic ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op(_), \A s \in S : op(s) \in Nat,
        NEW e, e \notin S, op(e) \in Nat
    PROVE MapThenSumSet(op, S \cup {e}) >= MapThenSumSet(op, S)
PROOF
    <1>1. IsFiniteSet(S \cup {e}) BY FS_Union, FS_Singleton
    <1>q. QED BY <1>1, CardSumMonotonic, MapThenSumSetDefined

LEMMA MapThenSumSetMonotonicOpGE ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op1(_), \A s \in S : op1(s) \in Nat,
        NEW op2(_), \A s \in S : op2(s) \in Nat,
        \A s \in S : op2(s) >= op1(s)
    PROVE
        MapThenSumSet(op2, S) >= MapThenSumSet(op1, S)
PROOF
    <1> DEFINE
        C1 == CardSum(S, op1)
        C2 == CardSum(S, op2)
        M1 == MapThenSumSet(op1, S)
        M2 == MapThenSumSet(op2, S)
    <1> HIDE DEF C1, C2, M1, M2
    <1> SUFFICES M2 >= M1 BY DEF M1, M2
    <1>1. C2 >= C1 BY CardSumMonotonicOpGE, Isa DEF C1, C2
    <1>2. M1 = C1 BY MapThenSumSetDefined, Isa DEF M1, C1
    <1>3. M2 = C2 BY MapThenSumSetDefined, Isa DEF M2, C2
    <1>q. QED BY <1>1, <1>2, <1>3

LEMMA MapThenSumSetMonotonicOpGT ==
    ASSUME
        NEW S, IsFiniteSet(S),
        NEW op1(_), \A s \in S : op1(s) \in Nat,
        NEW op2(_), \A s \in S : op2(s) \in Nat,
        \A s \in S : op2(s) >= op1(s),
        \E s \in S : op2(s) > op1(s)
    PROVE
        MapThenSumSet(op2, S) > MapThenSumSet(op1, S)
PROOF
    <1> DEFINE
        C1 == CardSum(S, op1)
        C2 == CardSum(S, op2)
        M1 == MapThenSumSet(op1, S)
        M2 == MapThenSumSet(op2, S)
    <1> HIDE DEF C1, C2, M1, M2
    <1> SUFFICES M2 > M1 BY DEF M1, M2
    <1>1. C2 > C1 BY CardSumMonotonicOpGT, Isa DEF C1, C2
    <1>2. M1 = C1 BY MapThenSumSetDefined, Isa DEF M1, C1
    <1>3. M2 = C2 BY MapThenSumSetDefined, Isa DEF M2, C2
    <1>q. QED BY <1>1, <1>2, <1>3

LEMMA MapThenSumSetZero ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A e \in S: op(e) \in Nat,
           MapThenSumSet(op, S) = 0
    PROVE \A e \in S: op(e) = 0
PROOF
    BY CardSumZero, MapThenSumSetDefined

LEMMA MapThenSumSetZeros ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op(_), \A e \in S: op(e) = 0
    PROVE MapThenSumSet(op, S) = 0
PROOF
    <1>0. \A e \in S: op(e) \in Nat OBVIOUS
    <1>1. MapThenSumSet(op, S) = CardSum(S, op) BY <1>0, MapThenSumSetDefined
    <1>q. QED BY <1>1, CardSumZeros

====
