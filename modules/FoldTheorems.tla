--------------------------- MODULE FoldTheorems ---------------------------
(*************************************************************************)
(* Theorems about the basic folding operator.                            *)
(* This module only lists theorem statements for reference. The proofs   *)
(* can be found in module FoldTheorems_proofs.tla.                       *)
(*************************************************************************)
EXTENDS Folds, FiniteSets, TLAPS

\* MapThenFoldSet is well-defined
THEOREM MapThenFoldSetDef ==
    ASSUME NEW op(_,_), NEW base, NEW f(_), NEW choose(_), NEW S,
           IsFiniteSet(S),
           \A T \in SUBSET S : T # {} => choose(T) \in T
    PROVE  MapThenFoldSet(op, base, f, choose, S) =
            IF S = {} THEN base
            ELSE LET x == choose(S)
                 IN  op(f(x), MapThenFoldSet(op, base, f, choose, S \ {x}))

\* folding the empty set yields the base value
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

\* type of a fold
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

(*************************************************************************)
(* Moreover, for an ACI operator with base as the neutral element,       *)
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
