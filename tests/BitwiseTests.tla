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

-----------------------------------------------------------------------------

ASSUME(\A n \in ZeroToM : AssertEq(shiftR(n, 1), (n \div 2)))

=============================================================================
