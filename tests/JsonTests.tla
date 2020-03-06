----------------------------- MODULE JsonTests -----------------------------
EXTENDS Json, Naturals, TLCExt

ASSUME(AssertEq(ToJson(<< >>), "[]"))
ASSUME(AssertEq(ToJson(<<"a", "b", "c">>), "[\"a\",\"b\",\"c\"]"))
ASSUME(AssertEq(ToJson([i \in 1..3 |-> "a"]), "{\"1\":\"a\",\"2\":\"a\",\"3\":\"a\"}"))
ASSUME(AssertEq(ToJson([ i \in {0,1,3} |-> "a" ]), "{\"0\":\"a\",\"1\":\"a\",\"3\":\"a\"}"))
ASSUME(AssertEq(ToJson([ i \in {0,1} |-> "a" ]), "{\"0\":\"a\",\"1\":\"a\"}"))
ASSUME(AssertEq(ToJson([ i \in {1} |-> "a" ]), "{\"1\":\"a\"}"))

ASSUME(AssertEq(ToJsonArray(<< >>), "[]"))
ASSUME(AssertEq(ToJsonArray(<<"a", "b", "c">>), "[\"a\",\"b\",\"c\"]"))

ASSUME(AssertEq(ToJsonObject(<< >>), "{}"))
ASSUME(AssertEq(ToJsonObject([ i \in {0,1,3} |-> "a" ]), "{\"0\":\"a\",\"1\":\"a\",\"3\":\"a\"}"))
ASSUME(AssertEq(ToJsonObject([ i \in {0,1} |-> "a" ]), "{\"0\":\"a\",\"1\":\"a\"}"))
ASSUME(AssertEq(ToJsonObject([ i \in {1} |-> "a" ]), "{\"1\":\"a\"}"))

=============================================================================
