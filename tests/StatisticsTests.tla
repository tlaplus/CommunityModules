------------------------- MODULE StatisticsTests -------------------------
EXTENDS Statistics

ASSUME LET T == INSTANCE TLC IN T!PrintT("StatisticsTests")

A ==
    [ i \in 1..6 |-> i ]

ASSUME( ChiSquare(A, A, "0.001"))
ASSUME( ChiSquare(A, A, "0.01"))
ASSUME( ChiSquare(A, A, "0.5"))
ASSUME(~ChiSquare([ i \in 1..6 |-> 6 ], A, "0.45"))
ASSUME(~ChiSquare([ i \in 1..6 |-> 6 ], A, "0.5"))
=============================================================================
