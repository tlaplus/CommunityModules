----------------------------- MODULE JsonTests -----------------------------
EXTENDS Json, TLCExt

ASSUME(AssertEq(ToJsonObject(<< >>), "{}"))
ASSUME(AssertEq(ToJsonObject([ i \in {0,1,3} |-> "a" ]), "{\"0\":\"a\",\"1\":\"a\",\"3\":\"a\"}"))
ASSUME(AssertEq(ToJsonObject([ i \in {0,1} |-> "a" ]), "{\"0\":\"a\",\"1\":\"a\"}"))
ASSUME(AssertEq(ToJsonObject([ i \in {1} |-> "a" ]), "{\"1\":\"a\"}"))

=============================================================================
