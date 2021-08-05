----- MODULE Counter -----
EXTENDS Naturals

ASSUME LET T == INSTANCE TLC IN T!PrintT("IOUtilsTests!C!b!Counter")

CONSTANT UpperBound

VARIABLE x

Init ==
    /\ x = 0

Next ==
    /\ x' = x + 1

Spec ==
    Init /\ [][Next]_x

Constraint ==
    /\ x < UpperBound

Inv ==
    /\ x < UpperBound

==========================