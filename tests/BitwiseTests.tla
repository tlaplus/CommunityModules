---------------------------- MODULE BitwiseTests ----------------------------
EXTENDS Bitwise, TLCExt, Naturals

ASSUME LET T == INSTANCE TLC IN T!PrintT("BitwiseTests")

ZeroToM == 0..99

LowBit(n) == IF n % 2 = 1 THEN 1 ELSE 0

-----------------------------------------------------------------------------

ASSUME(\A n \in ZeroToM : AssertEq(n & 0, 0))
ASSUME(\A n \in ZeroToM : AssertEq(0 & n, 0))
ASSUME(\A n \in ZeroToM : AssertEq(n & n, n))
ASSUME(\A n \in ZeroToM : AssertEq(n & 1, LowBit(n)))


AndPure(a, b) ==
    LET RECURSIVE AndR(_,_,_,_)
        AndR(x,y,n,m) == 
            LET exp == 2^n
            IN IF m = 0 
            THEN 0
            ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2) 
                        + AndR(x,y,n+1,m \div 2)
    IN IF a >= b THEN AndR(a,b,0,a) ELSE AndR(b,a,0,b)

ASSUME \A n, m \in 0..32 : AssertEq(n & m, AndPure(n,m))

-----------------------------------------------------------------------------

OrPure(a, b) ==
    LET RECURSIVE OrR(_,_,_,_)
        OrR(x,y,n,m) == 
            LET exp == 2^n
                xdm == (x \div exp) % 2
                ydm == (y \div exp) % 2
            IN IF m = 0 
                THEN 0
                ELSE exp * (((xdm + ydm) + (xdm * ydm)) % 2)
                            + OrR(x,y,n+1,m \div 2)
    IN IF a >= b THEN OrR(a,b,0,a) ELSE OrR(b,a,0,b)

ASSUME \A n, m \in 0..32 : AssertEq(n | m, OrPure(n,m))

-----------------------------------------------------------------------------

ASSUME(AssertEq(0 ^^ 0, 0))
ASSUME(AssertEq(1 ^^ 0, 1))
ASSUME(AssertEq(0 ^^ 1, 1))
ASSUME(AssertEq(1 ^^ 1, 0))

ASSUME(AssertEq(2 ^^ 0, 2))
ASSUME(AssertEq(1 ^^ 2, 3))
ASSUME(AssertEq(0 ^^ 2, 2))
ASSUME(AssertEq(2 ^^ 1, 3))

ASSUME(AssertEq(3 ^^ 0, 3))
ASSUME(AssertEq(3 ^^ 1, 2))
ASSUME(AssertEq(3 ^^ 2, 1))
ASSUME(AssertEq(0 ^^ 3, 3))
ASSUME(AssertEq(1 ^^ 3, 2))
ASSUME(AssertEq(2 ^^ 3, 1))

ASSUME(AssertEq(4 ^^ 0, 4))
ASSUME(AssertEq(4 ^^ 1, 5))
ASSUME(AssertEq(4 ^^ 2, 6))
ASSUME(AssertEq(4 ^^ 3, 7))
ASSUME(AssertEq(0 ^^ 4, 4))
ASSUME(AssertEq(1 ^^ 4, 5))
ASSUME(AssertEq(2 ^^ 4, 6))
ASSUME(AssertEq(3 ^^ 4, 7))

ASSUME(AssertEq(5 ^^ 0, 5))
ASSUME(AssertEq(5 ^^ 1, 4))
ASSUME(AssertEq(5 ^^ 2, 7))
ASSUME(AssertEq(5 ^^ 3, 6))
ASSUME(AssertEq(5 ^^ 4, 1))
ASSUME(AssertEq(0 ^^ 5, 5))
ASSUME(AssertEq(1 ^^ 5, 4))
ASSUME(AssertEq(2 ^^ 5, 7))
ASSUME(AssertEq(3 ^^ 5, 6))
ASSUME(AssertEq(4 ^^ 5, 1))

\* identity
ASSUME(\A n \in ZeroToM : AssertEq(n ^^ 0, n))
ASSUME(\A n \in ZeroToM : AssertEq(0 ^^ n, n))
\* self-inverse
ASSUME(\A n \in ZeroToM : AssertEq(n ^^ n, 0))
\* commutative
ASSUME(\A n,m \in ZeroToM : AssertEq(n ^^ m, m ^^ n))
\* associative
ASSUME(\A n,m,l \in ZeroToM : AssertEq(n ^^ (m ^^ l), (n ^^ m) ^^ l))

\* diagonals top-left to bottom-right
ASSUME(\A n \in {m \in ZeroToM : m % 2 = 1} : AssertEq(n ^^ (n - 1), 1))

\* diagonals top-right to bottom-left
ASSUME(\A n \in 0..15 : AssertEq(n ^^ (15 - n), 15))
ASSUME(\A n \in 0..31 : AssertEq(n ^^ (31 - n), 31))
ASSUME(\A n \in 0..63 : AssertEq(n ^^ (63 - n), 63))

XorPure(a, b) ==
    LET RECURSIVE XorPureR(_,_,_,_)
        XorPureR(x,y,n,m) == 
               IF m = 0 
               THEN 0
               ELSE LET exp == 2 ^ n
                    IN exp * (((x \div exp) + (y \div exp)) % 2) 
                        + XorPureR(x,y,n+1,m \div 2)
    IN IF a >= b THEN XorPureR(a,b,0,a) ELSE XorPureR(b,a,0,b)

ASSUME \A n, m \in 0..32 : AssertEq(n ^^ m, XorPure(n,m))

-----------------------------------------------------------------------------

ASSUME(\A n \in ZeroToM : AssertEq(shiftR(n, 1), (n \div 2)))

=============================================================================
