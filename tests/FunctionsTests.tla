------------------------- MODULE FunctionsTests -------------------------
EXTENDS Functions, Naturals, TLC, TLCExt, FiniteSets

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

ASSUME 
    LET IsInjectivePure(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b \* Pure as in no Java module override.
    IN /\ \A f \in [{0,1,2} -> {0,1,2,3}] : IsInjectivePure(f) = IsInjective(f)
       /\ \A f \in [{"a","b","c"} -> {0,1,2,3}] : IsInjectivePure(f) = IsInjective(f)
       /\ \A f \in [{0,1,2,3} -> {"a","b","c"}] : IsInjectivePure(f) = IsInjective(f)

ASSUME FoldFunction(LAMBDA x,y: {x} \cup y, {}, <<1,2,1>>) = {1,2}

ASSUME FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, <<1,2>>, {}) = {}


=============================================================================
