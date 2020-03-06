----------------------------- MODULE JsonTests -----------------------------
EXTENDS Json, Integers, TLC, TLCExt

\* Empty values
ASSUME(AssertEq(ToJsonArray({}), "[]"))
ASSUME(AssertEq(ToJsonArray(<<>>), "[]"))
ASSUME(AssertEq(ToJsonArray(<<>>), "[]"))

\* Primitive values
ASSUME(AssertEq(ToJson(FALSE), "false"))
ASSUME(AssertEq(ToJson(1), "1"))
ASSUME(AssertEq(ToJson({TRUE, FALSE}), "[false,true]"))
ASSUME(AssertEq(ToJson({1}), "[1]"))
ASSUME(AssertEq(ToJsonArray({TRUE, FALSE}), "[false,true]"))
ASSUME(AssertEq(ToJsonArray({1}), "[1]"))
ASSUME(AssertEq(ToJsonArray({"foo"}), "[\"foo\"]"))
ASSUME(AssertEq(ToJsonObject([a |-> TRUE, b |-> FALSE]), "{\"a\":true,\"b\":false}"))
ASSUME(AssertEq(ToJsonObject([a |-> 1]), "{\"a\":1}"))
ASSUME(AssertEq(ToJsonObject([a |-> "b"]), "{\"a\":\"b\"}"))

\* Structural values
ASSUME(AssertEq(ToJson({3, 2, 1}), "[1,2,3]"))
ASSUME(AssertEq(ToJson(<<3, 2, 1>>), "[3,2,1]"))
ASSUME(AssertEq(ToJson([x \in {3, 2, 1} |-> 2 * x + 1]), "[3,5,7]"))
ASSUME(AssertEq(ToJson(3 :> "c" @@ 2 :> "b" @@ 1 :> "a"), "[\"a\",\"b\",\"c\"]"))
ASSUME(AssertEq(ToJson([ {2, 1} -> {"a", "b"} ]), "[[\"a\",\"a\"],[\"a\",\"b\"],[\"b\",\"a\"],[\"b\",\"b\"]]"))
ASSUME(AssertEq(ToJson([ {1, 0} -> {"a", "b"} ]), "[{\"0\":\"a\",\"1\":\"a\"},{\"0\":\"a\",\"1\":\"b\"},{\"0\":\"b\",\"1\":\"a\"},{\"0\":\"b\",\"1\":\"b\"}]"))
ASSUME(AssertEq(ToJson([a: {2, 1}, b: {"a", "b"}]), "[{\"a\":1,\"b\":\"a\"},{\"a\":1,\"b\":\"b\"},{\"a\":2,\"b\":\"a\"},{\"a\":2,\"b\":\"b\"}]"))
ASSUME(AssertEq(ToJson({2, 1} \X {"b", "a"}), "[[1,\"a\"],[1,\"b\"],[2,\"a\"],[2,\"b\"]]"))
ASSUME(AssertEq(ToJson(SUBSET {2, 1}), "[[],[1],[2],[1,2]]"))
ASSUME(AssertEq(ToJson(1..3), "[1,2,3]"))
ASSUME(AssertEq(ToJsonArray({3, 2, 1}), "[1,2,3]"))
ASSUME(AssertEq(ToJsonArray(<<3, 2, 1>>), "[3,2,1]"))
ASSUME(AssertEq(ToJsonArray([x \in {3, 2, 1} |-> 2 * x + 1]), "[3,5,7]"))
ASSUME(AssertEq(ToJsonArray(3 :> "c" @@ 2 :> "b" @@ 1 :> "a"), "[\"a\",\"b\",\"c\"]"))
ASSUME(AssertEq(ToJsonArray([ {2, 1} -> {"a", "b"} ]), "[[\"a\",\"a\"],[\"a\",\"b\"],[\"b\",\"a\"],[\"b\",\"b\"]]"))
ASSUME(AssertEq(ToJsonArray([ {1, 0} -> {"a", "b"} ]), "[{\"0\":\"a\",\"1\":\"a\"},{\"0\":\"a\",\"1\":\"b\"},{\"0\":\"b\",\"1\":\"a\"},{\"0\":\"b\",\"1\":\"b\"}]"))
ASSUME(AssertEq(ToJsonArray([a: {2, 1}, b: {"a", "b"}]), "[{\"a\":1,\"b\":\"a\"},{\"a\":1,\"b\":\"b\"},{\"a\":2,\"b\":\"a\"},{\"a\":2,\"b\":\"b\"}]"))
ASSUME(AssertEq(ToJsonArray({2, 1} \X {"b", "a"}), "[[1,\"a\"],[1,\"b\"],[2,\"a\"],[2,\"b\"]]"))
ASSUME(AssertEq(ToJsonArray(SUBSET {2, 1}), "[[],[1],[2],[1,2]]"))
ASSUME(AssertEq(ToJsonArray(1..3), "[1,2,3]"))
ASSUME(AssertEq(ToJsonObject([a |-> FALSE, b |-> 1]), "{\"a\":false,\"b\":1}"))
ASSUME(AssertEq(ToJsonObject("a" :> 1 @@ "b" :> 2 @@ "c" :> 3), "{\"a\":1,\"b\":2,\"c\":3}"))
ASSUME(AssertEq(ToJsonObject(1 :> "b" @@ 0 :> "c"), "{\"0\":\"c\",\"1\":\"b\"}"))

\* Nested values
ASSUME(AssertEq(ToJsonObject([a |-> {<<1, 2>>}, b |-> [c |-> 3]]), "{\"a\":[[1,2]],\"b\":{\"c\":3}}"))

=============================================================================
