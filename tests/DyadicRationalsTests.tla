------------------------- MODULE DyadicRationalsTests -------------------------
EXTENDS DyadicRationals

ASSUME LET T == INSTANCE TLC IN T!PrintT("DyadicRationalsTests")

ASSUME(Half(One) = [num |-> 1, den |-> 2])
ASSUME(Half([num |-> 1, den |-> 2]) = [num |-> 1, den |-> 4])
ASSUME(Half([num |-> 1, den |-> 4]) = [num |-> 1, den |-> 8])
ASSUME(Half([num |-> 1, den |-> 8]) = [num |-> 1, den |-> 16])
ASSUME(Half([num |-> 1, den |-> 16]) = [num |-> 1, den |-> 32])
ASSUME(Half([num |-> 1, den |-> 32]) = [num |-> 1, den |-> 64])
ASSUME(Half([num |-> 1, den |-> 64]) = [num |-> 1, den |-> 128])
ASSUME(Half([num |-> 1, den |-> 128]) = [num |-> 1, den |-> 256])
ASSUME(Half([num |-> 1, den |-> 256]) = [num |-> 1, den |-> 512])

ASSUME(Half([num |-> 2, den |-> 8]) = [num |-> 1, den |-> 8])

-----------------------------------------------------------------------------

(***************************************************************************)
(* Reduce is LOCAL to DyadicRationals, so its Java override is checked via *)
(* Add and Half against copies of their definitions that use a pure       *)
(* Reduce.  The pure GCD is undefined for a zero numerator, hence only     *)
(* positive numerators.                                                    *)
(***************************************************************************)
LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSetsExt

LOCAL GCDPure(n, m) ==
    LET Divisors(q) == {d \in 1..q : \E e \in 1..q : q = d * e}
    IN Max(Divisors(n) \cap Divisors(m))

LOCAL ReducePure(p) ==
    LET gcd == GCDPure(p.num, p.den)
    IN  IF gcd = 1 THEN p
        ELSE [num |-> p.num \div gcd, den |-> p.den \div gcd]

LOCAL AddPure(p, q) ==
    IF p = Zero THEN q ELSE
    LET lcn == Max({p.den, q.den})
        qq == [num |-> q.num * (lcn \div q.den), den |-> q.den * (lcn \div q.den)]
        pp == [num |-> p.num * (lcn \div p.den), den |-> p.den * (lcn \div p.den)]
    IN ReducePure([num |-> qq.num + pp.num, den |-> lcn])

LOCAL HalfPure(p) ==
    ReducePure([num |-> p.num, den |-> p.den * 2])

LOCAL SomeDyadics ==
    [num : 1..9, den : {1, 2, 4, 8, 16}]

ASSUME \A p \in SomeDyadics : Half(p) = HalfPure(p)
ASSUME \A p, q \in SomeDyadics : Add(p, q) = AddPure(p, q)
=============================================================================
