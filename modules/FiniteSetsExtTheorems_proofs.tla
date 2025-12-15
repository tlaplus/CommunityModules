----------------- MODULE FiniteSetsExtTheorems_proofs -----------------------
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

THEOREM FoldSetACAddElement ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, 
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           NEW S \in SUBSET Typ, IsFiniteSet(S),
           NEW x \in Typ \ S
    PROVE  FoldSet(op, base, S \union {x}) = op(x, FoldSet(op, base, S))
<1>. /\ \A T : T # {} => (CHOOSE t \in T : TRUE) \in T 
     /\ \A s \in S \union {x} : s \in Typ
  OBVIOUS
<1>. QED  BY MapThenFoldSetACAddElement, Isa DEF FoldSet

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

THEOREM SumSetAddElement ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in Int \ S
    PROVE  SumSet(S \union {x}) = x + SumSet(S)
<1>. DEFINE op(i,j) == i + j
<1>1. /\ 0 \in Int
      /\ \A i,j \in Int : op(i,j) \in Int
      /\ \A i,j \in Int : op(i,j) = op(j,i)
      /\ \A i,j,k \in Int : op(i, op(j,k)) = op(op(i,j), k)
  OBVIOUS
<1>. HIDE DEF op 
<1>2. FoldSet(op, 0, S \union {x}) = op(x, FoldSet(op, 0, S))
  BY <1>1, FoldSetACAddElement, IsaM("iprover")
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

THEOREM ProductSetAddElement ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in Int \ S
    PROVE  ProductSet(S \union {x}) = x * ProductSet(S)
<1>. DEFINE op(i,j) == i * j
<1>1. /\ 1 \in Int
      /\ \A i,j \in Int : op(i,j) \in Int
      /\ \A i,j \in Int : op(i,j) = op(j,i)
      /\ \A i,j,k \in Int : op(i, op(j,k)) = op(op(i,j), k)
  OBVIOUS
<1>. HIDE DEF op 
<1>2. FoldSet(op, 1, S \union {x}) = op(x, FoldSet(op, 1, S))
  BY <1>1, FoldSetACAddElement, IsaM("iprover")
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

THEOREM MapThenSumSetAddElement ==
    ASSUME NEW S, IsFiniteSet(S), NEW x, x \notin S,
           NEW op(_), \A s \in S \union {x} : op(s) \in Int
    PROVE  MapThenSumSet(op, S \union {x}) = op(x) + MapThenSumSet(op, S)
<1>. \A T \in SUBSET S \union {x} : T # {} => (CHOOSE t \in T : TRUE) \in T 
  OBVIOUS
<1>. /\ 0 \in Int 
     /\ \A i,j \in Int : i+j \in Int
     /\ \A i,j \in Int : i+j = j+i 
     /\ \A i,j,k \in Int : i+(j+k) = (i+j)+k
  OBVIOUS
<1>. QED  BY MapThenFoldSetACAddElement, IsaM("iprover") DEF MapThenSumSet 

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
