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

ASSUME(AssertError("The argument of IsInjective should be a sequence, but instead it is:\n{}", IsInjective({})))
ASSUME(AssertError("The argument of IsInjective should be a sequence, but instead it is:\n[a: 1, b: 2]", IsInjective([a: 1, b: 2])))
ASSUME(AssertError("The argument of IsInjective should be a sequence, but instead it is:\n(0 :> 0 @@ 1 :> 1 @@ 2 :> 2)", IsInjective([i \in 0..2 |-> i])))

=============================================================================
