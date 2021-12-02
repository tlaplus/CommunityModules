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

ASSUME(\A n \in ZeroToM : AssertEq(shiftR(n, 1), (n \div 2)))

=============================================================================
