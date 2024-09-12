------------------------- MODULE RelationTests -------------------------
EXTENDS Relation, Naturals, TLC

ASSUME LET T == INSTANCE TLC IN T!PrintT("RelationTests")

S == {0, 1, 2, 3}

ASSUME IsReflexiveUnder(=, S)
ASSUME ~IsReflexiveUnder(<, S)
ASSUME IsReflexiveUnder(<=, S)

ASSUME ~IsIrreflexiveUnder(=, S)
ASSUME IsIrreflexiveUnder(<, S)
ASSUME ~IsIrreflexiveUnder(<=, S)

ASSUME IsSymmetricUnder(=, S)
ASSUME ~IsSymmetricUnder(<, S)
ASSUME ~IsSymmetricUnder(<=, S)

ASSUME LET R == [<<x,y>> \in S \X S |-> <(x,y)]
           T == <<0,2>> :> TRUE @@ <<2,0>> :> TRUE @@ R
       IN ~IsAntiSymmetric(T, S)

ASSUME IsAntiSymmetricUnder(=, S)
ASSUME IsAntiSymmetricUnder(<, S)
ASSUME IsAntiSymmetricUnder(<=, S)

ASSUME ~IsAsymmetricUnder(=, S)
ASSUME IsAsymmetricUnder(<, S)
ASSUME ~IsAsymmetricUnder(<=, S)

ASSUME LET R == [<<x,y>> \in S \X S |-> <(x,y)]
           T == <<0,2>> :> FALSE @@ R
       IN ~IsTransitive(T, S)

ASSUME IsTransitiveUnder(=, S)
ASSUME IsTransitiveUnder(<, S)
ASSUME IsTransitiveUnder(<=, S)

ASSUME ~IsStrictlyPartiallyOrderedUnder(=, S)
ASSUME IsStrictlyPartiallyOrderedUnder(<, S)
ASSUME ~IsStrictlyPartiallyOrderedUnder(<=, S)

ASSUME IsPartiallyOrderedUnder(=, S)
ASSUME ~IsPartiallyOrderedUnder(<, S)
ASSUME IsPartiallyOrderedUnder(<=, S)

ASSUME ~IsStrictlyTotallyOrderedUnder(=, S)
ASSUME IsStrictlyTotallyOrderedUnder(<, S)
ASSUME ~IsStrictlyTotallyOrderedUnder(<=, S)

ASSUME ~IsTotallyOrderedUnder(=, S)
ASSUME ~IsTotallyOrderedUnder(<, S)
ASSUME IsTotallyOrderedUnder(<=, S)
=============================================================================
