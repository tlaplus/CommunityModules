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
=============================================================================
