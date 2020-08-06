------------------------- MODULE SequencesExtTests -------------------------
EXTENDS Sequences, SequencesExt, Naturals, TLC, TLCExt, FiniteSets

ASSUME(ToSet(<<>>) = {})
ASSUME(ToSet(<<1>>) = {1})
ASSUME(ToSet(<<1,1>>) = {1})
ASSUME(ToSet(<<1,2,3>>) = {1,2,3})
ASSUME(ToSet([i \in 1..10 |-> 42]) = {42})
ASSUME(ToSet([i \in 1..10 |-> i]) = 1..10)
ASSUME(ToSet(Tail([i \in 1..10 |-> i])) = 2..10)
ASSUME(ToSet([i \in 0..9 |-> 42]) = {42})

ASSUME(IsInjective(<<>>))
ASSUME(IsInjective(<<1>>))
ASSUME(IsInjective(<<1,2,3>>))
ASSUME(~IsInjective(<<1,1>>))
ASSUME(~IsInjective(<<1,1,2,3>>))

ASSUME(IsInjective([i \in 1..10 |-> i]))
ASSUME(IsInjective([i \in 1..10 |-> {i}]))
ASSUME(IsInjective([i \in 1..10 |-> {i}]))
ASSUME(~IsInjective([i \in 1..10 |-> {1,2,3}]))

ASSUME(AssertError("The argument of IsInjective should be a sequence, but instead it is:\n{}", IsInjective({})))
ASSUME(AssertError("The argument of IsInjective should be a sequence, but instead it is:\n[a: 1, b: 2]", IsInjective([a: 1, b: 2])))
ASSUME(AssertError("The argument of IsInjective should be a sequence, but instead it is:\n(0 :> 0 @@ 1 :> 1 @@ 2 :> 2)", IsInjective([i \in 0..2 |-> i])))

ASSUME(SetToSeq({}) = <<>>)
ASSUME(SetToSeq({1}) = <<1>>)
ASSUME(LET s == {"t","l","a","p","l","u","s"}
           seq == SetToSeq(s)
       IN Len(seq) = Cardinality(s) /\ ToSet(seq) = s)

ASSUME(Reverse(<<>>) = <<>>)
ASSUME(Reverse(<<1,2,3>>) = <<3,2,1>>)
ASSUME(Reverse(<<1,1,2>>) = <<2,1,1>>)
ASSUME(Reverse(<<"a","a","b">>) = <<"b","a","a">>)

-----------------------------------------------------------------------------

ASSUME(Remove(<<>>, "c") = <<>>)
ASSUME(Remove(<<"a","a","b">>, "a") = <<"b">>)
ASSUME(Remove(<<"a","a","a">>, "a") = <<>>)
ASSUME(Remove(<<"a","a","b">>, "c") = <<"a","a","b">>)
ASSUME(Remove(<<{"a", "b"}, {"a","c"}>>, {"c", "a"}) = <<{"a", "b"}>>)

ASSUME(ReplaceAll(<<>>, 1, 4) = <<>>)
ASSUME(ReplaceAll(<<1,1,2,1,1,3>>, 1, 4) = <<4,4,2,4,4,3>>)

ASSUME(ReplaceAt(<<1>>, 1, 2) = <<2>>) 
ASSUME(ReplaceAt(<<1,1,1>>, 1, 2) = <<2,1,1>>) 

-----------------------------------------------------------------------------

ASSUME(IsPrefix(<<>>, <<>>))
ASSUME(IsPrefix(<<>>, <<1>>))
ASSUME(IsPrefix(<<1>>, <<1,2>>))
ASSUME(IsPrefix(<<1,2>>, <<1,2>>))
ASSUME(IsPrefix(<<1,2>>, <<1,2,3>>))

ASSUME(~IsPrefix(<<1,2,3>>, <<1,2>>))
ASSUME(~IsPrefix(<<1,2,2>>, <<1,2,3>>))
ASSUME(~IsPrefix(<<1,2,3>>, <<1,2,2>>))
ASSUME(~IsPrefix(<<1>>, <<2>>))
ASSUME(~IsPrefix(<<2>>, <<1>>))
ASSUME(~IsPrefix(<<2,1>>, <<1,2>>))
ASSUME(~IsPrefix(<<1,2>>, <<2,1>>))

ASSUME(~IsStrictPrefix(<<>>, <<>>))
ASSUME(IsStrictPrefix(<<>>, <<1>>))
ASSUME(IsStrictPrefix(<<1>>, <<1,2>>))
ASSUME(~IsStrictPrefix(<<1,2>>, <<1,2>>))
ASSUME(IsStrictPrefix(<<1,2>>, <<1,2,3>>))

ASSUME(IsSuffix(<<3>>, <<1,2,3>>))
ASSUME(IsSuffix(<<2,3>>, <<1,2,3>>))
ASSUME(~IsSuffix(<<3,2>>, <<1,2,3>>))
ASSUME(IsSuffix(<<1,2,3>>, <<1,2,3>>))

ASSUME(~IsStrictSuffix(<<1,2,3>>, <<1,2,3>>))

-----------------------------------------------------------------------------

ASSUME(~Contains(<<>>, 3))
ASSUME(Contains(<<3>>, 3))
ASSUME(~Contains(<<3>>, 4))
ASSUME(Contains(<<3,4>>, 3))
ASSUME(Contains(<<3,4>>, 4))


ASSUME(Contains(<<{3},{4}>>, {4}))
ASSUME(Contains(<<{3},{4}>>, {3}))
ASSUME(~Contains(<<{3},{4}>>, {2}))

=============================================================================
