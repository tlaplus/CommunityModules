--------------------------- MODULE FoldsTheorems --------------------------
(*************************************************************************)
(* Theorems about the basic folding operator.                            *)
(* This module only lists theorem statements for reference. The proofs   *)
(* can be found in module FoldsTheorems_proofs.tla.                      *)
(*************************************************************************)
EXTENDS Folds, FiniteSets

(*************************************************************************)
(* MapThenFoldSet is well-defined, i.e., it conforms to the equation     *)
(* used for defining the operator.                                       *)
(*************************************************************************)
THEOREM MapThenFoldSetDef ==
    ASSUME NEW op(_,_), NEW base, NEW f(_), NEW choose(_), NEW S,
           IsFiniteSet(S),
           \A T \in SUBSET S : T # {} => choose(T) \in T
    PROVE  MapThenFoldSet(op, base, f, choose, S) =
            IF S = {} THEN base
            ELSE LET x == choose(S)
                 IN  op(f(x), MapThenFoldSet(op, base, f, choose, S \ {x}))

(*************************************************************************)
(* The following two theorems correspond to the two cases in the         *)
(* equation in theorem MapThenFoldSetDef, but are easier to use.         *)
(*************************************************************************)
THEOREM MapThenFoldSetEmpty ==
    ASSUME NEW op(_,_), NEW base, NEW f(_), NEW choose(_)
    PROVE  MapThenFoldSet(op, base, f, choose, {}) = base

\* fold of a non-empty set
THEOREM MapThenFoldSetNonempty ==
    ASSUME NEW op(_,_), NEW base, NEW f(_), NEW choose(_), NEW S, S # {},
           IsFiniteSet(S),
           \A T \in SUBSET S : T # {} => choose(T) \in T
    PROVE  MapThenFoldSet(op, base, f, choose, S) = 
            LET x == choose(S)
            IN  op(f(x), MapThenFoldSet(op, base, f, choose, S \ {x}))

(*************************************************************************)
(* Folding over two finite sets S and T that are related by a bijection  *)
(* that is compatible with the choice and mapping functions yields the   *)
(* same result.                                                          *)
(*************************************************************************)
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

(*************************************************************************)
(* In particular, folding over the same set, using two mapping functions *)
(* that agree over the elements of the set, yields the same result.      *)
(*************************************************************************)
THEOREM MapThenFoldSetEqual ==
    ASSUME NEW op(_,_), NEW base, NEW choose(_), NEW S, IsFiniteSet(S),
           \A T \in SUBSET S : T # {} => choose(T) \in T,
           NEW f(_), NEW g(_), 
           \A s \in S : f(s) = g(s)
    PROVE  MapThenFoldSet(op, base, f, choose, S) = 
           MapThenFoldSet(op, base, g, choose, S)

(*************************************************************************)
(* The type of a fold corresponds to the type associated with the binary *)
(* operator that underlies the fold.                                     *)
(*************************************************************************)
THEOREM MapThenFoldSetType ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW Typ, NEW op(_,_), NEW base \in Typ, NEW f(_), NEW choose(_),
           \A t,u \in Typ : op(t,u) \in Typ,
           \A s \in S : f(s) \in Typ,
           \A T \in SUBSET S : T # {} => choose(T) \in T
    PROVE  MapThenFoldSet(op, base, f, choose, S) \in Typ

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

===========================================================================
