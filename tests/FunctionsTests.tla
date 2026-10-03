------------------------- MODULE FunctionsTests -------------------------
EXTENDS Functions, Integers, TLC, TLCExt, FiniteSets, Sequences

ASSUME LET T == INSTANCE TLC IN T!PrintT("FunctionsTests")

ASSUME RestrictDomain([x \in 0 .. 9 |-> x*x], LAMBDA x : x % 2 = 0)
       = (0 :> 0 @@ 2 :> 4 @@ 4 :> 16 @@ 6 :> 36 @@ 8 :> 64)

ASSUME RestrictValues([x \in 0 .. 9 |-> x*x], LAMBDA y : y % 4 = 0)
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

ASSUME(IsInjective([a |-> 1, b |-> 2]))
ASSUME(~IsInjective([a |-> 1, b |-> 1]))
\* The function constructor is not evaluated to an explicit function in this context.
ASSUME((IF IsInjective([b \in BOOLEAN |-> FALSE]) THEN <<1>> ELSE <<2>>)[1] = 2)
ASSUME((IF IsInjective([b \in BOOLEAN |-> b]) THEN <<1>> ELSE <<2>>)[1] = 1)

\* Assert that Functions#isInjectiveDestructive is side-effect free.
SomeSeq == UNION {[1..m -> {1,2}] : m \in 0..Cardinality({1,2})}
SomeExp == CHOOSE x \in SomeSeq: IsInjective(x) /\ Len(x) > 3
ASSUME Cardinality(SomeSeq) = 7

ASSUME 
    LET IsInjectivePure(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b \* Pure as in no Java module override.
    IN /\ \A f \in [{0,1,2} -> {0,1,2,3}] : IsInjectivePure(f) = IsInjective(f)
       /\ \A f \in [{"a","b","c"} -> {0,1,2,3}] : IsInjectivePure(f) = IsInjective(f)
       /\ \A f \in [{0,1,2,3} -> {"a","b","c"}] : IsInjectivePure(f) = IsInjective(f)
       /\ \A f \in [a : {0,1,2}, b : {0,1,2}, c : {0,1,2}] : IsInjectivePure(f) = IsInjective(f)

ASSUME FoldFunction(LAMBDA x,y: {x} \cup y, {}, <<1,2,1>>) = {1,2}

ASSUME FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, <<1,2>>, {}) = {}

ASSUME FoldFunction(LAMBDA x,y: {x} \cup y, {}, [n \in 1..9999 |-> n]) = 1..9999

ASSUME FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, [n \in 1..9999 |-> n], {}) = {}

ASSUME FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, [n \in 1..9999 |-> n], 2..9998) = 2..9998

\* FoldFunction and FoldFunctionOnSet do not fix the order in which they combine
\* elements, so they are only compared on operators for which the order does not matter.
ASSUME
    LET FoldFunctionOnSetPure(op(_,_), base, fun, indices) ==
            MapThenFoldSet(op, base, LAMBDA i : fun[i], LAMBDA s: CHOOSE x \in s : TRUE, indices)
        FoldFunctionPure(op(_,_), base, fun) ==
            FoldFunctionOnSetPure(op, base, fun, DOMAIN fun)
        Check(f) ==
          /\ FoldFunction(+, 0, f) = FoldFunctionPure(+, 0, f)
          /\ FoldFunction(LAMBDA x,y: {x} \cup y, {}, f) = FoldFunctionPure(LAMBDA x,y: {x} \cup y, {}, f)
          /\ \A I \in SUBSET DOMAIN f :
                /\ FoldFunctionOnSet(+, 0, f, I) = FoldFunctionOnSetPure(+, 0, f, I)
                /\ FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, f, I) = FoldFunctionOnSetPure(LAMBDA x,y: {x} \cup y, {}, f, I)
    IN /\ \A f \in [{1,2,3} -> {-1,0,2}] : Check(f)
       /\ \A f \in [{"a","b","c"} -> {-1,0,2}] : Check(f)

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
    IN /\ \A f \in [{0,1,2} -> {0,1,2,3}] : InversePure(f, DOMAIN f, Range(f)) = AntiFunction(f)
       /\ \A f \in [{"a","b","c"} -> {0,1,2,3}] : InversePure(f, DOMAIN f, Range(f)) = AntiFunction(f)
       /\ \A f \in [{0,1,2,3} -> {"a","b","c"}] : InversePure(f, DOMAIN f, Range(f)) = AntiFunction(f)

ASSUME AntiFunction(<<1, 1>>) = <<1>>
ASSUME AntiFunction(<<2, 1, 2>>) = (1 :> 2 @@ 2 :> 1)
ASSUME AntiFunction([a |-> 0, b |-> 0, c |-> 1]) = (0 :> "a" @@ 1 :> "c")
      
SomeVal ==
	[n1 |-> "n3", n2 |-> "n1", n3 |-> "n2"]
	
SomeDerivedVal[ i \in 0..2 ] == 
	IF i = 0 THEN "n1" ELSE SomeVal[SomeDerivedVal[i-1]]
     
ASSUME
	/\ AntiFunction(SomeDerivedVal) = [n1 |-> 0, n2 |-> 2, n3 |-> 1]
	/\ SomeDerivedVal = (0 :> "n1" @@ 2 :> "n2" @@ 1 :> "n3")

ASSUME
	LET F == [n1 |-> 0, n2 |-> 2, n3 |-> 1]
	IN AntiFunction(F) = (0 :> "n1" @@ 2 :> "n2" @@ 1 :> "n3")

ASSUME
	LET F == [n1 |-> 0, n2 |-> 2, n3 |-> 1]
	IN AntiFunction(AntiFunction(F)) = F

ASSUME
	LET F == (0 :> "n1" @@ 2 :> "n2" @@ 1 :> "n3")
	IN AntiFunction(AntiFunction(F)) = F

ASSUME
    LET f == ("a" :> 0 @@ "b" :> 1 @@ "c" :> 2)
        g == ("a" :> 1 @@ "b" :> 1 @@ "c" :> 3)
    IN Pointwise(f,g,+) = ("a" :> 1 @@ "b" :> 2 @@ "c" :> 5 )

ASSUME
    LET f == ("a" :> 1 @@ "b" :> 1 @@ "c" :> 2)
        g == ("a" :> 1 @@ "b" :> 1 @@ "c" :> 3)
    IN Pointwise(f,g,-) = ("a" :> 0 @@ "b" :> 0 @@ "c" :> (-1) )

ASSUME IsRestriction(<<>>, <<>>)
ASSUME IsRestriction(<<>>, [one |-> 1])
ASSUME IsRestriction([one |-> 1], [one |-> 1, two |-> 2])
ASSUME IsRestriction([one |-> 1], [one |-> 1])
ASSUME ~IsRestriction([one |-> 1], <<>>)
ASSUME ~IsRestriction([one |-> 1], [two |-> 2])
ASSUME ~IsRestriction([one |-> 1, two |-> 2], [two |-> 2])
ASSUME ~IsRestriction([one |-> 1, two |-> 2], [one |-> 1, two |-> 3])

=============================================================================
