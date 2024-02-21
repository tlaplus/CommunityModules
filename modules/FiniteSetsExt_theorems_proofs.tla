---- MODULE FiniteSetsExt_theorems_proofs ----
EXTENDS FiniteSetsExt, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems, TLAPS
(*
Initial hints are found [Proofs on recursive functions](https://groups.google.com/g/tlaplus/c/eHJYc_voNB0).
The general idea is taken from `FiniteSetTheorems_proofs.tla'.
*)



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
