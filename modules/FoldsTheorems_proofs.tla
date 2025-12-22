------------------------ MODULE FoldsTheorems_proofs ----------------------
(*************************************************************************)
(* Theorems about the basic folding operator.                            *)
(*************************************************************************)
EXTENDS Folds, FiniteSets, TLAPS
LOCAL INSTANCE FiniteSetTheorems
LOCAL INSTANCE FunctionTheorems
LOCAL INSTANCE WellFoundedInduction

\* MapThenFoldSet is well-defined
THEOREM MapThenFoldSetDef ==
    ASSUME NEW op(_,_), NEW base, NEW f(_), NEW choose(_), NEW S,
           IsFiniteSet(S),
           \A T \in SUBSET S : T # {} => choose(T) \in T
    PROVE  MapThenFoldSet(op, base, f, choose, S) =
            IF S = {} THEN base
            ELSE LET x == choose(S)
                 IN  op(f(x), MapThenFoldSet(op, base, f, choose, S \ {x}))
<1>. DEFINE FoldDef(g, s) ==
                IF s = {} THEN base
                ELSE LET x == choose(s) IN op(f(x), g[s \ {x}])
            iter(T) == CHOOSE g : g = [s \in SUBSET T |-> FoldDef(g, s)]
<1>1. ASSUME NEW T \in SUBSET S, NEW U \in SUBSET T
      PROVE  iter(T)[U] = FoldDef(iter(T), U)
  <2>. FiniteSubsetsOf(T) = SUBSET T
    BY FS_Subset, FS_FiniteSubsetsOfFinite
  <2>1. IsWellFoundedOn(StrictSubsetOrdering(T), FiniteSubsetsOf(T))
    BY FS_Subset, FS_StrictSubsetOrderingWellFounded
  <2>2. WFDefOn(StrictSubsetOrdering(T), FiniteSubsetsOf(T), FoldDef)
    BY DEF WFDefOn, SetLessThan, StrictSubsetOrdering
  <2>3. OpDefinesFcn(iter(T), FiniteSubsetsOf(T), FoldDef)
    BY Zenon DEF MapThenFoldSet, OpDefinesFcn
  <2>. HIDE DEF FoldDef
  <2>4. WFInductiveDefines(iter(T), SUBSET T, FoldDef)
    BY <2>1, <2>2, <2>3, WFInductiveDef, Isa
  <2>. QED  BY <2>4 DEF WFInductiveDefines
<1>. HIDE DEF iter
<1>2. ASSUME NEW T \in SUBSET S, NEW U \in SUBSET T
      PROVE  iter(S)[U] = iter(T)[U]
  <2>. DEFINE P(V) == iter(S)[V] = iter(T)[V]
  <2>1. IsFiniteSet(U)
    BY FS_Subset
  <2>2. ASSUME NEW V \in SUBSET U,
               \A W \in (SUBSET V) \ {V} : P(W)
        PROVE  P(V)
    <3>1. /\ iter(S)[V] = FoldDef(iter(S), V)
          /\ iter(T)[V] = FoldDef(iter(T), V)
      BY <1>1
    <3>2. CASE V = {}
      BY <3>1, <3>2
    <3>3. CASE V # {}
      <4>. DEFINE x == choose(V)  W == V \ {x}
      <4>1. /\ FoldDef(iter(S), V) = op(f(x), iter(S)[W])
            /\ FoldDef(iter(T), V) = op(f(x), iter(T)[W])
        BY <3>3
      <4>2. W \in (SUBSET V) \ {V}
        BY <3>3
      <4>. QED  BY <2>2, <3>1, <4>1, <4>2
    <3>. QED  BY <3>2, <3>3
  <2>3. P(U)
    <3>. HIDE DEF P 
    <3>. QED  BY ONLY <2>1, <2>2, FS_WFInduction, IsaM("blast")
  <2>. QED  BY <2>3
<1>3. MapThenFoldSet(op, base, f, choose, S) = iter(S)[S]
  BY Zenon DEF MapThenFoldSet, iter
<1>4. @ = FoldDef(iter(S), S)
  BY <1>1, Zenon
<1>. DEFINE T == S \ {choose(S)}
<1>5. iter(S)[T] = iter(T)[T]
  BY <1>2
<1>6. iter(T)[T] = MapThenFoldSet(op, base, f, choose, T)
  BY Zenon DEF MapThenFoldSet, iter
<1>. QED  BY <1>3, <1>4, <1>5, <1>6

\* folding the empty set yields the base value
THEOREM MapThenFoldSetEmpty ==
    ASSUME NEW op(_,_), NEW base, NEW f(_), NEW choose(_)
    PROVE  MapThenFoldSet(op, base, f, choose, {}) = base
<1>1. /\ IsFiniteSet({})
      /\ \A T \in SUBSET {} : T # {} => choose(T) \in T
  BY FS_EmptySet
<1>2. MapThenFoldSet(op, base, f, choose, {}) = 
      IF {} = {} THEN base
      ELSE LET x == choose({})
           IN  op(f(x), MapThenFoldSet(op, base, f, choose, {} \ {x}))
  BY <1>1, MapThenFoldSetDef, IsaM("iprover")
<1>. QED  BY <1>2

\* fold of a non-empty set
THEOREM MapThenFoldSetNonempty ==
    ASSUME NEW op(_,_), NEW base, NEW f(_), NEW choose(_), NEW S, S # {},
           IsFiniteSet(S),
           \A T \in SUBSET S : T # {} => choose(T) \in T
    PROVE  MapThenFoldSet(op, base, f, choose, S) = 
            LET x == choose(S)
            IN  op(f(x), MapThenFoldSet(op, base, f, choose, S \ {x}))
BY MapThenFoldSetDef, Isa

\* equality of MapThenFoldSet for a bijection that behaves homomorphically
THEOREM MapThenFoldSetBijection ==
    ASSUME NEW op(_,_), NEW base,
           NEW S, IsFiniteSet(S), NEW fS(_), NEW chS(_),
           \A U \in SUBSET S : U # {} => chS(U) \in U,
           NEW T, IsFiniteSet(T), NEW fT(_), NEW chT(_),
           \A U \in SUBSET T : U # {} => chT(U) \in U,
           NEW bij(_),
           \A s \in S : bij(s) \in T,
           \A t \in T : \E s \in S : bij(s) = t,
           \A s1, s2 \in S : bij(s1) = bij(s2) => s1 = s2,
           \A s \in S : fS(s) = fT(bij(s)),
           \A U \in SUBSET S : U # {} => bij(chS(U)) = chT({bij(s) : s \in U})
    PROVE  MapThenFoldSet(op, base, fS, chS, S) = MapThenFoldSet(op, base, fT, chT, T)
<1>. DEFINE P(U) == MapThenFoldSet(op, base, fS, chS, U) =
                    MapThenFoldSet(op, base, fT, chT, {bij(s) : s \in U})
<1>1. ASSUME NEW U \in SUBSET S, \A V \in (SUBSET U) \ {U} : P(V)
      PROVE  P(U)
  <2>1. CASE U = {}
    BY <2>1, MapThenFoldSetEmpty, Isa 
  <2>2. CASE U # {}
    <3>. DEFINE BU == {bij(s) : s \in U}
                xS == chS(U)     xT == chT(BU)   
                VS == U \ {xS}   VT == BU \ {xT}
    <3>. SUFFICES MapThenFoldSet(op, base, fS, chS, U) =
                  MapThenFoldSet(op, base, fT, chT, BU)
      OBVIOUS
    <3>1. /\ IsFiniteSet(U)
          /\ \A V \in SUBSET U : V # {} => chS(V) \in V 
      BY <2>2, FS_Subset
    <3>2. MapThenFoldSet(op, base, fS, chS, U) =
          op(fS(xS), MapThenFoldSet(op, base, fS, chS, VS))
      BY <2>2, <3>1, MapThenFoldSetNonempty, Isa 
    <3>3. IsFiniteSet(BU)
      BY <3>1, FS_Image, Isa
    <3>4. /\ BU # {}
          /\ \A V \in SUBSET BU : V # {} => chT(V) \in V 
      BY <2>2
    <3>5. MapThenFoldSet(op, base, fT, chT, BU) =
          op(fT(xT), MapThenFoldSet(op, base, fT, chT, VT))
      <4>. HIDE DEF BU 
      <4>. QED  BY <3>3, <3>4, MapThenFoldSetNonempty, Isa
    <3>6. /\ xS \in U 
          /\ xT = bij(xS)
          /\ fS(xS) = fT(xT)
          /\ VT = {bij(s) : s \in VS}
      BY <2>2, <3>1
    <3>7. P(VS)
      BY <1>1, <3>6
    <3>. HIDE DEF BU, xS, xT, VS, VT
    <3>. QED  BY <3>2, <3>5, <3>6, <3>7
  <2>. QED  BY <2>1, <2>2
<1>2. P(S)
  BY <1>1, FS_WFInduction, IsaM("iprover")
<1>3. {bij(s) : s \in S} = T
  OBVIOUS
<1>. QED  BY <1>2, <1>3

\* special case when the bijection is the identity
THEOREM MapThenFoldSetEqual ==
    ASSUME NEW op(_,_), NEW base, NEW choose(_), NEW S, IsFiniteSet(S),
           \A T \in SUBSET S : T # {} => choose(T) \in T,
           NEW f(_), NEW g(_), 
           \A s \in S : f(s) = g(s)
    PROVE  MapThenFoldSet(op, base, f, choose, S) = 
           MapThenFoldSet(op, base, g, choose, S)
<1>. DEFINE id(s) == s 
<1>1. /\ \A s \in S : id(s) \in S
      /\ \A t \in S : \E s \in S : id(s) = t
      /\ \A s1, s2 \in S : id(s1) = id(s2) => s1 = s2
      /\ \A s \in S : f(s) = g(id(s))
      /\ \A U \in SUBSET S : U # {} => id(choose(U)) = choose({id(s) : s \in U})
  BY Zenon
<1>. HIDE DEF id
<1>. QED  BY <1>1, MapThenFoldSetBijection, IsaM("iprover")

\* type of a fold
THEOREM MapThenFoldSetType ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW Typ, NEW op(_,_), NEW base \in Typ, NEW f(_), NEW choose(_),
           \A t,u \in Typ : op(t,u) \in Typ,
           \A s \in S : f(s) \in Typ,
           \A T \in SUBSET S : T # {} => choose(T) \in T
    PROVE  MapThenFoldSet(op, base, f, choose, S) \in Typ
<1>1. ASSUME NEW T \in SUBSET S,
             \A U \in (SUBSET T) \ {T} : MapThenFoldSet(op, base, f, choose, U) \in Typ
      PROVE  MapThenFoldSet(op, base, f, choose, T) \in Typ
  <2>1. CASE T = {}
    BY <2>1, MapThenFoldSetEmpty, Zenon
  <2>2. CASE T # {}
    <3>. DEFINE x == choose(T)  U == T \ {x}
    <3>1. /\ IsFiniteSet(T)
          /\ \A V \in SUBSET T : V # {} => choose(V) \in V
      BY FS_Subset
    <3>2. MapThenFoldSet(op, base, f, choose, T) =
          op(f(x), MapThenFoldSet(op, base, f, choose, U))
      BY ONLY <2>2, <3>1, MapThenFoldSetNonempty, Isa
    <3>. QED  BY <1>1, <2>2, <3>2
  <2>. QED  BY <2>1, <2>2
<1>. QED  BY <1>1, FS_WFInduction, IsaM("iprover")

(*************************************************************************)
(* In many applications the operator used for folding is associative and *)
(* commutative. In that case, the following theorem may be more useful   *)
(* for reasoning about folding a non-empty set.                          *)
(*************************************************************************)
THEOREM MapThenFoldSetAC ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, NEW f(_),
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           NEW S, IsFiniteSet(S), NEW x \in S,
           NEW choose(_), \A T \in SUBSET S : T # {} => choose(T) \in T,
           \A s \in S : f(s) \in Typ
    PROVE  MapThenFoldSet(op, base, f, choose, S) = 
           op(f(x), MapThenFoldSet(op, base, f, choose, S \ {x}))
<1>. DEFINE P(U) == \A y \in U : MapThenFoldSet(op, base, f, choose, U) = 
                                 op(f(y), MapThenFoldSet(op, base, f, choose, U \ {y}))
<1>1. ASSUME NEW U \in SUBSET S,
             \A V \in (SUBSET U) \ {U} : P(V)
      PROVE  P(U)
  <2>1. IsFiniteSet(U)
    BY FS_Subset
  <2>. SUFFICES ASSUME NEW y \in U 
                PROVE  MapThenFoldSet(op, base, f, choose, U) = 
                       op(f(y), MapThenFoldSet(op, base, f, choose, U \ {y}))
    OBVIOUS
  <2>. DEFINE z == choose(U)
  <2>2. /\ U # {}
        /\ \A T \in SUBSET U : T # {} => choose(T) \in T 
    OBVIOUS
  <2>3. MapThenFoldSet(op, base, f, choose, U) = op(f(z), MapThenFoldSet(op, base, f, choose, U \ {z}))
    BY <2>1, <2>2, MapThenFoldSetNonempty, IsaM("iprover")
  <2>4. CASE z # y
    <3>1. /\ y \in U \ {z}
          /\ U \ {z} \in (SUBSET U) \ {U}
          /\ IsFiniteSet(U \ {z})
          /\ IsFiniteSet((U \ {z}) \ {y})
      BY <2>1, <2>4, FS_RemoveElement
    <3>a. /\ \A u \in U \ {z} : f(u) \in Typ
          /\ \A T \in SUBSET (U \ {z}) : T # {} => choose(T) \in T
          /\ \A u \in (U \ {z}) \ {y} : f(u) \in Typ
          /\ \A T \in SUBSET ((U \ {z}) \ {y}) : T # {} => choose(T) \in T
      OBVIOUS
    <3>2. /\ MapThenFoldSet(op, base, f, choose, U \ {z}) \in Typ
          /\ MapThenFoldSet(op, base, f, choose, (U \ {z}) \ {y}) \in Typ
      BY <3>1, <3>a, MapThenFoldSetType, Isa
    <3>3. MapThenFoldSet(op, base, f, choose, U \ {z}) = 
          op(f(y), MapThenFoldSet(op, base, f, choose, (U \ {z}) \ {y}))
      BY <1>1, <3>1
    <3>4. op(f(z), op(f(y), MapThenFoldSet(op, base, f, choose, (U \ {z}) \ {y}))) =
          op(f(y), op(f(z), MapThenFoldSet(op, base, f, choose, (U \ {z}) \ {y})))
      BY <3>2
    <3>5. /\ (U \ {z}) \ {y} = (U \ {y}) \ {z}
          /\ z \in U \ {y}
          /\ U \ {y} \in (SUBSET U) \ {U}
          /\ IsFiniteSet(U \ {y})
      BY <2>1, <2>4, FS_RemoveElement
    <3>6. MapThenFoldSet(op, base, f, choose, U \ {y}) = 
          op(f(z), MapThenFoldSet(op, base, f, choose, (U \ {y}) \ {z}))
      BY <1>1, <3>5
    <3>. QED  BY <2>3, <3>3, <3>4, <3>5, <3>6
  <2>. QED  BY <2>3, <2>4
<1>. QED  
  <2>. HIDE DEF P 
  <2>. P(S)  BY <1>1, FS_WFInduction, IsaM("iprover")
  <2>. QED   BY DEF P

\* reformulation for adding an element to the set
THEOREM MapThenFoldSetACAddElement ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, NEW f(_),
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           NEW S, IsFiniteSet(S), NEW x, x \notin S,
           NEW choose(_), \A T \in SUBSET S \union {x} : T # {} => choose(T) \in T,
           \A s \in S \union {x} : f(s) \in Typ
    PROVE  MapThenFoldSet(op, base, f, choose, S \union {x}) = 
           op(f(x), MapThenFoldSet(op, base, f, choose, S))
<1>. DEFINE U == S \union {x}
<1>1. MapThenFoldSet(op, base, f, choose, U) = 
      op(f(x), MapThenFoldSet(op, base, f, choose, U \ {x}))
  <2>. /\ IsFiniteSet(U)
       /\ x \in U 
       /\ U \ {x} = S 
       /\ \A T \in SUBSET U : T # {} => choose(T) \in T 
       /\ \A s \in U : f(s) \in Typ 
    BY FS_AddElement
  <2>. HIDE DEF U 
  <2>. QED  BY MapThenFoldSetAC, IsaM("iprover")
<1>. QED  BY <1>1, Zenon

(*************************************************************************)
(* Moreover, for an AC operator with base as the neutral element,        *)
(* folding commutes with set union, for disjoint sets.                   *)
(*************************************************************************)
THEOREM MapThenFoldSetDisjointUnion ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, NEW f(_),
           \A t,u \in Typ : op(t,u) \in Typ,
           \A t,u \in Typ : op(t,u) = op(u,t),
           \A t,u,v \in Typ : op(t, op(u,v)) = op(op(t,u),v),
           \A t \in Typ : op(base, t) = t,
           NEW S, IsFiniteSet(S),
           NEW T, IsFiniteSet(T), S \cap T = {},
           NEW choose(_), 
           \A U \in SUBSET (S \union T) : U # {} => choose(U) \in U,
           \A x \in S \union T : f(x) \in Typ
    PROVE  MapThenFoldSet(op, base, f, choose, S \union T) = 
           op(MapThenFoldSet(op, base, f, choose, S),
              MapThenFoldSet(op, base, f, choose, T))
<1>. DEFINE P(U) == MapThenFoldSet(op, base, f, choose, U \union T) = 
                    op(MapThenFoldSet(op, base, f, choose, U),
                       MapThenFoldSet(op, base, f, choose, T))
<1>1. MapThenFoldSet(op, base, f, choose, T) \in Typ
  <2>. /\ \A U \in SUBSET T : U # {} => choose(U) \in U 
       /\ \A x \in T : f(x) \in Typ
    OBVIOUS
  <2>. QED  BY MapThenFoldSetType, IsaM("iprover")
<1>2. P({})
  BY <1>1, MapThenFoldSetEmpty, Isa
<1>3. ASSUME NEW U \in SUBSET S, IsFiniteSet(U), P(U), NEW x \in S \ U
      PROVE  P(U \union {x})
  <2>1. /\ IsFiniteSet((U \union {x}) \union T)
        /\ x \in (U \union {x}) \union T
        /\ \A y \in (U \union {x}) \union T : f(y) \in Typ
        /\ \A V \in SUBSET ((U \union {x}) \union T) : V # {} => choose(V) \in V
    BY <1>3, FS_Union, FS_AddElement
  <2>2. MapThenFoldSet(op, base, f, choose, (U \union {x}) \union T) =
        op(f(x), MapThenFoldSet(op, base, f, choose, ((U \union {x}) \union T) \ {x}))
    BY <2>1, MapThenFoldSetAC, IsaM("iprover")
  <2>3. ((U \union {x}) \union T) \ {x} = U \union T
    OBVIOUS
  <2>4. MapThenFoldSet(op, base, f, choose, U \union T) =
        op(MapThenFoldSet(op, base, f, choose, U), MapThenFoldSet(op, base, f, choose, T))
    BY <1>3
  <2>5. /\ IsFiniteSet(U \union {x})
        /\ x \in U \union {x}
        /\ \A y \in U \union {x} : f(y) \in Typ
        /\ \A V \in SUBSET (U \union {x}) : V # {} => choose(V) \in V
    BY <1>3, FS_AddElement
  <2>6. /\ IsFiniteSet(U)
        /\ \A y \in U  : f(y) \in Typ
        /\ \A V \in SUBSET U : V # {} => choose(V) \in V
    BY <1>3
  <2>7. MapThenFoldSet(op, base, f, choose, U) \in Typ 
    BY <2>6, MapThenFoldSetType, Isa
  <2>8. op(f(x), op(MapThenFoldSet(op, base, f, choose, U), MapThenFoldSet(op, base, f, choose, T))) =
        op(op(f(x), MapThenFoldSet(op, base, f, choose, U)), MapThenFoldSet(op, base, f, choose, T))
    BY <1>1, <2>7
  <2>9. MapThenFoldSet(op, base, f, choose, U \union {x}) =
        op(f(x), MapThenFoldSet(op, base, f, choose, (U \union {x}) \ {x}))
    BY <2>5, MapThenFoldSetAC, IsaM("iprover")
  <2>10. (U \union {x}) \ {x} = U 
    OBVIOUS
  <2>. QED  BY <2>2, <2>3, <2>4, <2>8, <2>9, <2>10
<1>. QED
  <2>. HIDE DEF P 
  <2>. P(S)  BY <1>2, <1>3, FS_Induction, IsaM("iprover")
  <2>. QED   BY DEF P 

===========================================================================
