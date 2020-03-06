----------------------------- MODULE JsonTests -----------------------------
EXTENDS Integers, Json, TLC, TLCExt

\* Empty values
ASSUME(AssertEq(ToJsonObject({}), "[]"))
ASSUME(AssertEq(ToJsonObject(<<>>), "[]"))

\* Primitive values
ASSUME(AssertEq(ToJsonObject({TRUE, FALSE}), "[false, true]"))
ASSUME(AssertEq(ToJsonObject({1}), "[1]"))
ASSUME(AssertEq(ToJsonObject({"foo"}), "[\"foo\"]"))

\* Structural values
ASSUME(AssertEq(ToJsonObject([a |-> FALSE, b |-> 1]), "{\"a\": false, \"b\": 1}"))
ASSUME(AssertEq(ToJsonObject({3, 2, 1}), "[1, 2, 3]"))
ASSUME(AssertEq(ToJsonObject(<<3, 2, 1>>), "[3, 2, 1]"))
ASSUME(AssertEq(ToJsonObject([x \in {3, 2, 1} |-> 2 * x + 1]), "[3, 5, 7]"))
ASSUME(AssertEq(ToJsonObject("a" :> 1 @@ "b" :> 2 @@ "c" :> 3), "{\"a\": 1, \"b\": 2, \"c\": 3}"))
ASSUME(AssertEq(ToJsonObject(3 :> "c" @@ 2 :> "b" @@ 1 :> "a"), "[\"a\", \"b\", \"c\"]"))
ASSUME(AssertEq(ToJsonObject(1 :> "b" @@ 0 :> "c"), "{\"0\": \"c\", \"1\": \"b\"}"))
ASSUME(AssertEq(ToJsonObject([ {2, 1} -> {"a", "b"} ]), "[[\"a\", \"a\"], [\"a\", \"b\"], [\"b\", \"a\"], [\"b\", \"b\"]]"))
ASSUME(AssertEq(ToJsonObject([ {1, 0} -> {"a", "b"} ]), "[{\"0\": \"a\", \"1\": \"a\"}, {\"0\": \"a\", \"1\": \"b\"}, {\"0\": \"b\", \"1\": \"a\"}, {\"0\": \"b\", \"1\": \"b\"}]"))
ASSUME(AssertEq(ToJsonObject([a: {2, 1}, b: {"a", "b"}]), "[{\"a\": 1, \"b\": \"a\"}, {\"a\": 1, \"b\": \"b\"}, {\"a\": 2, \"b\": \"a\"}, {\"a\": 2, \"b\": \"b\"}]"))
ASSUME(AssertEq(ToJsonObject({2, 1} \X {"b", "a"}), "[[1, \"a\"], [1, \"b\"], [2, \"a\"], [2, \"b\"]]"))
ASSUME(AssertEq(ToJsonObject(SUBSET {2, 1}), "[[], [1], [2], [1, 2]]"))
ASSUME(AssertEq(ToJsonObject(1..3), "[1, 2, 3]"))

\* Nested values
ASSUME(AssertEq(ToJsonObject([a |-> {<<1, 2>>}, b |-> [c |-> 3]]), "{\"a\": [[1, 2]], \"b\": {\"c\": 3}}"))

=============================================================================
