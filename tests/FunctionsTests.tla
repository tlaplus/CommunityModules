------------------------- MODULE FunctionsTests -------------------------
EXTENDS Functions, Naturals, TLC, TLCExt, FiniteSets, Sequences

ASSUME LET T == INSTANCE TLC IN T!PrintT("FunctionsTests")

ASSUME SelectDomain([x \in 0 .. 9 |-> x*x], LAMBDA x : x % 2 = 0)
       = (0 :> 0 @@ 2 :> 4 @@ 4 :> 16 @@ 6 :> 36 @@ 8 :> 64)

ASSUME SelectValues([x \in 0 .. 9 |-> x*x], LAMBDA y : y % 4 = 0)
       = (0 :> 0 @@ 2 :> 4 @@ 4 :> 16 @@ 6 :> 36 @@ 8 :> 64)

ASSUME(IsInjective(<<>>))
ASSUME(IsInjective(<<1>>))
ASSUME(IsInjective(<<1,2,3>>))
ASSUME(~IsInjective(<<1,1>>))
ASSUME(~IsInjective(<<1,1,2,3>>))

ASSUME(IsInjective([i \in 1..10 |-> i]))
ASSUME(IsInjective([i \in 1..10 |-> {i}]))
ASSUME(IsInjective([i \in 1..10 |-> {i}]))
ASSUME(~IsInjective([i \in 1..10 |-> {1,2,3}]))

ASSUME(IsInjective([a: 1, b: 2]))
ASSUME(~IsInjective([a: 1, b: 1]))
ASSUME(IsInjective([a: {1}, b: {2}]))
ASSUME(~IsInjective([a: {1}, b: {1}]))
ASSUME(~IsInjective("a" :> 1 @@ "b" :> 1))
ASSUME(IsInjective("a" :> 1 @@ "a" :> 1))
ASSUME(IsInjective("a" :> [i \in 0..2 |-> i] @@ "b" :> [i \in 1..3 |-> i]))
ASSUME(~IsInjective("a" :> [i \in 0..2 |-> i] @@ "b" :> [i \in 0..2 |-> i]))
ASSUME(~IsInjective({"a"} :> [i \in 0..2 |-> i] @@ {"b"} :> [i \in 0..2 |-> i]))
ASSUME(IsInjective([i \in 0..2 |-> i]))
ASSUME(IsInjective( "a":> [{1,2} -> {3,4}] @@ "b":> [{1,2} -> {3,5}] ))
ASSUME(AssertError("The argument of IsInjective should be a function, but instead it is:\n{}", IsInjective({})))

\* Assert that Functions#isInjectiveDestructive is side-effect free.
SomeSeq == UNION {[1..m -> {1,2}] : m \in 0..Cardinality({1,2})}
SomeExp == CHOOSE x \in SomeSeq: IsInjective(x) /\ Len(x) > 3
ASSUME Cardinality(SomeSeq) = 7

ASSUME 
    LET IsInjectivePure(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b \* Pure as in no Java module override.
    IN /\ \A f \in [{0,1,2} -> {0,1,2,3}] : IsInjectivePure(f) = IsInjective(f)
       /\ \A f \in [{"a","b","c"} -> {0,1,2,3}] : IsInjectivePure(f) = IsInjective(f)
       /\ \A f \in [{0,1,2,3} -> {"a","b","c"}] : IsInjectivePure(f) = IsInjective(f)

ASSUME FoldFunction(LAMBDA x,y: {x} \cup y, {}, <<1,2,1>>) = {1,2}

ASSUME FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, <<1,2>>, {}) = {}

ASSUME FoldFunction(LAMBDA x,y: {x} \cup y, {}, [n \in 1..9999 |-> n]) = 1..9999

ASSUME FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, [n \in 1..9999 |-> n], {}) = {}

ASSUME FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, [n \in 1..9999 |-> n], 2..9998) = 2..9998

ASSUME AssertError(
           "The third argument of FoldFunction should be a function, but instead it is:\nTRUE",
           FoldFunction(+, 23, TRUE))

ASSUME AssertError(
           "The fourth argument of FoldFunctionOnSet should be a set, but instead it is:\nTRUE",
           FoldFunctionOnSet(+, 23, <<>>, TRUE))

ASSUME AssertError(
           "The third argument of FoldFunctionOnSet should be a function, but instead it is:\nTRUE",
           FoldFunctionOnSet(+, 23, TRUE, {}))

\* AntiFunction
ASSUME AntiFunction(<<"a", "b", "c">>) = [a |-> 1, b |-> 2, c |-> 3]

ASSUME 
    LET InversePure(f, S, T) == [t \in T |-> CHOOSE s \in S : t \in Range(f) => f[s] = t] \* "Pure" as in no Java module override.
    IN /\ \A f \in [{0,1,2} -> {0,1,2,3}] : IsInjective(f) => InversePure(f, DOMAIN f, Range(f)) = AntiFunction(f)
       /\ \A f \in [{"a","b","c"} -> {0,1,2,3}] : IsInjective(f) => InversePure(f, DOMAIN f, Range(f)) = AntiFunction(f)
       /\ \A f \in [{0,1,2,3} -> {"a","b","c"}] : IsInjective(f) => InversePure(f, DOMAIN f, Range(f)) = AntiFunction(f)
      

=============================================================================
