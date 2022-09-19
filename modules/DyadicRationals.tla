-------------------------- MODULE DyadicRationals ---------------------------
\* https://en.wikipedia.org/wiki/Dyadic_rational
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSetsExt
LOCAL INSTANCE TLC

LOCAL Divides(p, q) == 
    \E d \in 1..q : q = p * d

LOCAL Divisors(q) ==
    {d \in 1..q : Divides(d, q)}

LOCAL GCD(n, m) ==
    Max(Divisors(n) \cap Divisors(m))

------------------------------------------------------------------------------

LOCAL Rational(num, den) ==
    [num |-> num, den |-> den]

LOCAL Reduce(p) ==
    LET gcd == GCD(p.num, p.den)
    IN  IF gcd = 1 THEN p
        ELSE Rational(p.num \div gcd, p.den \div gcd)

IsDyadicRational(r) ==
    \E i \in 0..r.den: 2^i = r.den 

Zero == Rational(0,1)

One == Rational(1,1)

Add(p, q) ==
    IF p = Zero THEN q ELSE
    LET lcn == Max({p.den, q.den}) \* shortcut because dyadic!
        qq == Rational(q.num * (lcn \div q.den), q.den * (lcn \div q.den))
        pp == Rational(p.num * (lcn \div p.den), p.den * (lcn \div p.den))
    IN Reduce(Rational(qq.num + pp.num, lcn))

Half(p) ==
    Reduce(Rational(p.num, p.den * 2))

PrettyPrint(p) ==
    IF p = Zero THEN "0" ELSE
    IF p = One THEN "1" ELSE
    ToString(p.num) \o "/" \o ToString(p.den)

===============================================================================
\* Modification History
\* Last modified Mon Dec 27 17:52:54 PST 2021 by Markus Kuppe
\* Created Sun Dec 26 01:36:40 PDT 2021 by Markus Kuppe