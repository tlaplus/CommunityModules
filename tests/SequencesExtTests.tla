------------------------- MODULE SequencesExtTests -------------------------
EXTENDS Sequences, SequencesExt, Integers, TLC, TLCExt, FiniteSets, FiniteSetsExt, Functions

ASSUME LET T == INSTANCE TLC IN T!PrintT("SequencesExtTests")

ASSUME(ToSet(<<>>) = {})
ASSUME(ToSet(<<1>>) = {1})
ASSUME(ToSet(<<1,1>>) = {1})
ASSUME(ToSet(<<1,2,3>>) = {1,2,3})
ASSUME(ToSet([i \in 1..10 |-> 42]) = {42})
ASSUME(ToSet([i \in 1..10 |-> i]) = 1..10)
ASSUME(ToSet(Tail([i \in 1..10 |-> i])) = 2..10)
ASSUME(ToSet([i \in 0..9 |-> 42]) = {42})

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

-----------------------------------------------------------------------------

ASSUME LET cons(x,y) == <<x, y>>
       IN FoldLeft(cons, 10, <<13,11,12>> ) = << << <<10, 13>>, 11 >>, 12>>

ASSUME FoldLeft(+, 1, [n \in 1..25 |-> n]) =  326
ASSUME FoldLeft(-, 1, [n \in 1..25 |-> n]) = -324

ASSUME FoldLeft(+, 1, [n \in 1..250 |-> n]) =  31376
ASSUME FoldLeft(-, 1, [n \in 1..250 |-> n]) = -31374

ASSUME LET cons(x,y) == <<x, y>>
       IN FoldRight(cons, <<23,21,22>>, 20 ) = <<23, <<21, <<22, 20>> >> >>

ASSUME FoldRight(+, [n \in 1..25 |-> n], 1) = 326
ASSUME FoldRight(-, [n \in 1..25 |-> n], 1) =  12

ASSUME FoldRight(+, [n \in 1..250 |-> n], 1) = 31376
ASSUME FoldRight(-, [n \in 1..250 |-> n], 1) =  -124

ASSUME FoldSeq(  LAMBDA e, acc: acc + 1, 0, <<1,1,1,1,1>>) = 5
ASSUME FoldLeft( LAMBDA acc, e: acc + 1, 0, <<1,1,1,1,1>>) = 5
ASSUME FoldRight(LAMBDA e, acc: acc + 1, <<1,1,1,1,1>>, 0) = 5

ASSUME AssertError(
           "The second argument of FoldRight should be a sequence, but instead it is:\nTRUE",
           FoldRight(+, TRUE, 23))

ASSUME AssertError(
           "The third argument of FoldLeft should be a sequence, but instead it is:\nTRUE",
           FoldLeft(+, 23, TRUE))

\* Error comes from Functions!FoldFunctionOnSet
ASSUME AssertError(
           "The third argument of FoldFunction should be a function, but instead it is:\nTRUE",
           FoldSeq(+, 23, TRUE))

-----------------------------------------------------------------------------

ASSUME LongestCommonPrefix({<<>>}) = <<>>
ASSUME LongestCommonPrefix({<<1>>,<<2>>,<<3>>}) = <<>>
ASSUME LongestCommonPrefix({<<1>>,<<1>>,<<3>>}) = <<>>
ASSUME LongestCommonPrefix({<<2,3,3>>, <<2,2,3>>, <<2,3,3,4>>}) = <<2>>
ASSUME LongestCommonPrefix({<<2,3,3>>, <<2,3,3>>, <<2,3,3,4>>}) = <<2,3,3>>
ASSUME LongestCommonPrefix({<<2,3,3>>, <<2,3,3>>, <<1,3,3,4>>}) = <<>>
ASSUME LongestCommonPrefix({<<1,3,3,4>>, <<2,3,3>>, <<2,3,3>>}) = <<>>

ASSUME LongestCommonPrefix({<<[i \in 1..3|-> i], [i \in 1..3|-> i]>>, <<[i \in 1..3|-> i]>>}) = <<[i \in 1..3|-> i]>>
ASSUME LongestCommonPrefix({<<[i \in 1..3|-> i], [i \in 1..3|-> i]>>, <<[i \in 1..3|-> i+1]>>}) = <<>>


LOCAL LongestCommonPrefixPure(S) ==
    LET PrefixesPure(s) == { SubSeq(s, 1, l) : l \in 0..Len(s) }
        CommonPrefixesPure(T) == LET P == UNION { PrefixesPure(seq) : seq \in T }
                                 IN { prefix \in P : \A t \in S: IsPrefix(prefix, t) }
    IN CHOOSE longest \in CommonPrefixesPure(S):
          \A other \in CommonPrefixesPure(S):
              Len(other) <= Len(longest)

ASSUME LongestCommonPrefixPure(BoundedSeq({1,2,3}, 5)) = LongestCommonPrefix(BoundedSeq({1,2,3}, 5))

ASSUME \A s \in SUBSET BoundedSeq({0,1}, 3):
    \* For the empty set, the pure variant fails when choosing from the empty set.
    \* The Java module override throws an EvalException.
    s # {} => LongestCommonPrefix(s) = LongestCommonPrefixPure(s)

ASSUME LongestCommonPrefix({"abc", "abd"}) = "ab"
ASSUME LongestCommonPrefix({"abc", "a"}) = "a"
ASSUME LongestCommonPrefix({""}) = ""
ASSUME LongestCommonPrefix({"a", "b"}) = ""
ASSUME LongestCommonPrefix({"abc", "abcc", "abcd"}) = "abc"
ASSUME LongestCommonPrefix({"ab \"c", "ab \"cc", "ab \"cd"}) = "ab \"c"

ASSUME \A s \in SUBSET {"a","b","ab","ba","aa","bb"}:
    \* For the empty set, the pure variant fails when choosing from the empty set.
    \* The Java module override throws an EvalException.
    s # {} => LongestCommonPrefix(s) = LongestCommonPrefixPure(s)

-----------------------------------------------------------------------------

ASSUME FlattenSeq(<<>>) = <<>>
ASSUME FlattenSeq(<< <<1,2>>, <<1>> >>) = << 1, 2, 1 >>
ASSUME FlattenSeq(<< <<1,2>>, << << 1, 2 >> >> >>) = << 1, 2, << 1, 2 >> >>
ASSUME FlattenSeq("") = ""
ASSUME FlattenSeq(<< <<"a">>, <<"b">> >>) = <<"a", "b">>
ASSUME FlattenSeq(<<"a", "b">>) = "ab"

-----------------------------------------------------------------------------

ASSUME Zip(<<>>, <<>>) = << <<>>, <<>> >>
ASSUME Zip(<< <<>>  >>, <<1>>) = << << <<>> >>, <<1>> >>
ASSUME Zip(<<1>>, << <<>>  >>) = << <<1>>, << <<>> >> >>
ASSUME Zip(<<2>>,<<2>>) = << <<2>>, <<2>> >>
ASSUME Zip(<<2>>,<<3>>) = << <<2>>, <<3>> >>
ASSUME Zip(<<2,3>>,<<1,4>>) = << <<2>>, <<1>>, <<3>>, <<4>> >>
ASSUME Zip(<<2,3>>,<<2,3>>) = << <<2>>, <<2>>, <<3>>, <<3>> >>
ASSUME Zip(<<1,3>>,<<2,4>>) = <<<<1>>, <<2>>, <<3>>, <<4>>>>
ASSUME AssertEq(FlattenSeq(Zip(<<1,3>>,<<2,4>>)), <<1, 2, 3, 4>>)
ASSUME Zip(<<"a", "c">>, <<"b", "d">>) = <<<<"a">>, <<"b">>, <<"c">>, <<"d">>>>
ASSUME AssertEq(FlattenSeq(Zip(<<"a", "c">>, <<"b", "d">>)), <<"a", "b", "c", "d">>)

-----------------------------------------------------------------------------

ASSUME SubSeqs(<<>>) = {<<>>}
ASSUME SubSeqs(<<1>>) = {<<>>, <<1>>}
ASSUME SubSeqs(<<1,1>>) = {<<>>, <<1>>, <<1,1>>}
ASSUME SubSeqs(<<1,1,1>>) = {<<>>, <<1>>, <<1,1>>, <<1,1,1>>}
ASSUME SubSeqs(<<1,2,3,2>>) = {<<>>, <<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>, <<3, 2>>, <<1, 2, 3>>, <<2, 3, 2>>, <<1, 2, 3, 2>>}
ASSUME SubSeqs([i \in 1..3 |-> i]) = {<<>>, <<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>, <<1, 2, 3>>}

LOCAL ToSeq(fun) ==
    LET RECURSIVE toSeq(_,_)
        toSeq(f, d) ==
            IF d = {} THEN <<>> ELSE <<f[Min(d)]>> \o toSeq(f, d \ {Min(d)})
    IN toSeq(fun, DOMAIN fun)

LOCAL SubSeqsAlt(s) ==
    LET IsConsecutive(S) == S # {} => S = Min(S)..Max(S)
        DOMS == { sd \in SUBSET DOMAIN s : IsConsecutive(sd) }
    IN { ToSeq([ i \in d |-> s[i] ]) : d \in DOMS }

ASSUME \A seq \in BoundedSeq(1..5, 5) :
        /\ SubSeqs(seq) = SubSeqsAlt(seq)
        /\ LET ss == SubSeqs(seq)
           IN /\ <<>> \in ss
              /\ Cardinality(ss) \in 1..16
              /\ \A s \in ss :
                   /\ Len(s) <= Len(seq)
                   /\ Range(s) \subseteq Range(seq)

-----------------------------------------------------------------------------

ASSUME ReplaceFirstSubSeq(<<>>,<<>>,<<>>) = <<>>
ASSUME ReplaceFirstSubSeq(<<4>>,<<>>,<<>>) = <<4>>
ASSUME ReplaceFirstSubSeq(<<4>>,<<4>>,<<>>) = <<>>
ASSUME ReplaceFirstSubSeq(<<>>,<<>>,<<3,2,3,4>>) = <<3,2,3,4>>
ASSUME ReplaceFirstSubSeq(<<4,4>>,<<3,2,3,4>>,<<3,2,3,4>>) = <<4,4>>
ASSUME ReplaceFirstSubSeq(<<4,4>>,<<>>,<<3,2,3,4>>) = <<4,4,3,2,3,4>>

ASSUME ReplaceFirstSubSeq(<<4,4>>,<<4>>,<<3,2,3,4>>) = <<3,2,3,4,4>>
ASSUME ReplaceFirstSubSeq(<<>>,<<4>>,<<3,2,3,4>>) = <<3,2,3>>
ASSUME ReplaceFirstSubSeq(<<>>,<<4>>,<<3,2,3,4,4>>) = <<3,2,3,4>>
ASSUME ReplaceFirstSubSeq(<<4,4>>,<<3>>,<<3,2,3,4>>) = <<4,4,2,3,4>>
ASSUME ReplaceFirstSubSeq(<<4>>, <<1,2>>, <<1,2,1,2>>) = <<4,1,2>>
ASSUME ReplaceFirstSubSeq(<<4,4>>, <<1,2>>, <<1,2,1,2>>) = <<4,4,1,2>>
ASSUME ReplaceFirstSubSeq(<<4,4,4>>, <<1,2>>, <<1,2,1,2>>) = <<4,4,4,1,2>>

ASSUME ReplaceFirstSubSeq(<<1,2>>, <<1,2>>, <<1,2,2,1>>) = <<1,2,2,1>>
ASSUME ReplaceFirstSubSeq(<<2,1>>, <<1,2>>, <<1,2,2,1>>) = <<2,1,2,1>>

ASSUME \A seq \in (BoundedSeq(1..5, 5) \ {<<>>}):
    /\ ReplaceFirstSubSeq(<<6>>, <<>>, seq) = <<6>> \o seq
    /\ ReplaceFirstSubSeq(<<6>>, <<Head(seq)>>, seq) = <<6>> \o Tail(seq)

ASSUME ReplaceFirstSubSeq("", "", "") = ""
ASSUME ReplaceFirstSubSeq("a", "", "") = "a"
ASSUME ReplaceFirstSubSeq("a", "b", "") = ""
ASSUME ReplaceFirstSubSeq("a", "d", "abc") = "abc"
ASSUME ReplaceFirstSubSeq("ddd", "ab", "abab") = "dddab"
ASSUME ReplaceFirstSubSeq("ddd", "aa", "aaa") = "ddda"
ASSUME ReplaceFirstSubSeq("ddd", "abab", "abab") = "ddd"

ASSUME(ReplaceFirstSubSeq("\\", "%%", "Properly escape the %% char") = "Properly escape the \\ char")
ASSUME(ReplaceFirstSubSeq("\"", "%%", "Properly escape the %% char") = "Properly escape the \" char")
ASSUME(ReplaceFirstSubSeq("\n", "%%", "Properly escape the %% char") = "Properly escape the \n char")
ASSUME(ReplaceFirstSubSeq("\t", "%%", "Properly escape the %% char") = "Properly escape the \t char")
ASSUME(ReplaceFirstSubSeq("\f", "%%", "Properly escape the %% char") = "Properly escape the \f char")
ASSUME(ReplaceFirstSubSeq("\r", "%%", "Properly escape the %% char") = "Properly escape the \r char")

ASSUME ReplaceFirstSubSeq("\\\\", "\\", "Properly escape the \\quotes") = "Properly escape the \\\\quotes"
ASSUME ReplaceFirstSubSeq("replaces", "%pattern%", "This %pattern% the pattern") = "This replaces the pattern"

-----------------------------------------------------------------------------

ASSUME AssertEq(ReplaceAllSubSeqs(<<4>>,<<1>>,<<>>), <<>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<4>>,<<2>>,<<1>>), <<1>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<4>>,<<2>>,<<1,1>>), <<1,1>>)

ASSUME AssertEq(ReplaceAllSubSeqs(<<>>,<<>>,<<>>), <<>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<4>>,<<>>,<<>>), <<4>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<4,4>>,<<>>,<<>>), <<4,4>>)

ASSUME AssertEq(ReplaceAllSubSeqs(<<1>>, <<1>>, <<1>>), <<1>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<2>>, <<3>>, <<1,3>>), <<1,2>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<1,1>>, <<1>>, <<1,1>>), <<1,1,1,1>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<1,1>>, <<1,1>>, <<1,1>>), <<1,1>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<2,2>>, <<1,1>>, <<1,1,1>>), <<2,2,1>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<>>, <<1,1>>, <<1,1,1>>), <<1>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<2,2>>, <<1,1,1>>, <<1,1,1>>), <<2,2>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<>>, <<1,1,1>>, <<1,1,1>>), <<>>)
ASSUME AssertEq(ReplaceAllSubSeqs(<<2,2>>, <<1,1,1>>, <<1,1,1,1>>), <<2,2,1>>)

ASSUME AssertEq(ReplaceAllSubSeqs(<<1,1>>, <<>>, <<2,2>>), <<1,1,2,1,1,2>>)

ASSUME ReplaceAllSubSeqs("dd", "d", "dd") = "dddd"

ASSUME ReplaceAllSubSeqs("ddd", "a", "") = ""
ASSUME ReplaceAllSubSeqs("ddd", "", "") = "ddd"
ASSUME ReplaceAllSubSeqs("ddd", "ab", "abab") = "dddddd"
ASSUME ReplaceAllSubSeqs("ddd", "abab", "abab") = "ddd"

ASSUME ReplaceAllSubSeqs("ddd", "aa", "aaa") = "ddda"
ASSUME ReplaceAllSubSeqs("a", "a", "a") = "a"
ASSUME ReplaceAllSubSeqs("aa", "aa", "aa") = "aa"
ASSUME ReplaceAllSubSeqs("aa", "aa", "aaaa") = "aaaa"
ASSUME ReplaceAllSubSeqs("aa", "aa", "bbbb") = "bbbb"

ASSUME ReplaceAllSubSeqs("ddd", "", "abab") = "dddadddbdddadddb"

ASSUME(ReplaceAllSubSeqs("\\", "%%", "Properly escape the %% char") = "Properly escape the \\ char")
ASSUME(ReplaceAllSubSeqs("\"", "%%", "Properly escape the %% char") = "Properly escape the \" char")
ASSUME(ReplaceAllSubSeqs("\n", "%%", "Properly escape the %% char") = "Properly escape the \n char")
ASSUME(ReplaceAllSubSeqs("\t", "%%", "Properly escape the %% char") = "Properly escape the \t char")
ASSUME(ReplaceAllSubSeqs("\f", "%%", "Properly escape the %% char") = "Properly escape the \f char")
ASSUME(ReplaceAllSubSeqs("\r", "%%", "Properly escape the %% char") = "Properly escape the \r char")

ASSUME AssertEq(ReplaceAllSubSeqs("replaces", "%pattern%", "This %pattern% the pattern %pattern% multipe times"), "This replaces the pattern replaces multipe times")
ASSUME AssertEq(ReplaceAllSubSeqs("\\\\", "\\", "Properly escape the \\quotes"), "Properly escape the \\\\quotes")


-----------------------------------------------------------------------------

ASSUME AssertEq(SetToSeqs({}), {<<>>})
ASSUME AssertEq(SetToSeqs({"t"}), {<<"t">>})
ASSUME AssertEq(SetToSeqs({"t","l"}), {<<"t","l">>, <<"l","t">>})
ASSUME AssertEq(SetToSeqs({"t","l","a"}), {<<"t","l","a">>, <<"t","a","l">> , <<"l","t","a">>, <<"l","a","t">> , <<"a","t","l">>, <<"a","l","t">>})

SetToSeqsPure(S) ==
LET D == 1..Cardinality(S)
  IN { f \in [D -> S] : \A i,j \in D : i # j => f[i] # f[j] }

ASSUME AssertEq(SetToSeqs({}), SetToSeqsPure({}))
ASSUME AssertEq(SetToSeqs({"t"}), SetToSeqsPure({"t"}))
ASSUME AssertEq(SetToSeqs({"t","l"}), SetToSeqsPure({"t","l"}))
ASSUME AssertEq(SetToSeqs({"t","l","a"}), SetToSeqsPure({"t","l","a"}))

ASSUME AssertEq(SetToAllKPermutations({}), {<<>>})
ASSUME AssertEq(SetToAllKPermutations({"t"}), {<<>>, <<"t">>})
ASSUME AssertEq(SetToAllKPermutations({"t","l"}), {<<>>, <<"t">>, <<"l">>,<<"t","l">>, <<"l","t">>})
ASSUME AssertEq(SetToAllKPermutations({"t","l","a"}), {<< >>, 
                                        <<"a">>, <<"t">>, <<"l">>, 
                                        <<"a", "t">>, <<"a", "l">>, <<"t", "a">>, <<"t", "l">>, <<"l", "a">>, <<"l", "t">>, 
                                        <<"a", "t", "l">>, <<"a", "l", "t">>, <<"t", "a", "l">>, <<"t", "l", "a">>, <<"l", "a", "t">>, <<"l", "t", "a">>})

=============================================================================
