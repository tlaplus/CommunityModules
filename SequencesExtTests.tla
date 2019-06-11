------------------------- MODULE SequencesExtTests -------------------------
EXTENDS Sequences, SequencesExt, Naturals, TLC

ASSUME(IsASet(<<>>))
ASSUME(IsASet(<<1>>))
ASSUME(IsASet(<<1,2,3>>))
ASSUME(~IsASet(<<1,1>>))
ASSUME(~IsASet(<<1,1,2,3>>))

ASSUME(IsASet([i \in 1..10 |-> i]))
ASSUME(IsASet([i \in 1..10 |-> {i}]))
ASSUME(IsASet([i \in 1..10 |-> {i}]))
ASSUME(~IsASet([i \in 1..10 |-> {1,2,3}]))

=============================================================================
