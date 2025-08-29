---------------------------- MODULE SequencesExt ----------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt
LOCAL INSTANCE Functions
LOCAL INSTANCE Folds
LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

(*************************************************************************)  
(* Convert a sequence to the set of its elements (sequence image).       *)
(*                                                                       *)
(* Returns the set of all elements that appear in the sequence,          *)
(* effectively removing duplicates and order. The cardinality of the     *)
(* result is at most the length of the sequence.                         *)
(*                                                                       *)
(* Examples:                                                             *)
(*   ToSet(<<>>) = {}                                                    *)
(*   ToSet(<<1>>) = {1}                                                  *)
(*   ToSet(<<1,2,3>>) = {1,2,3}                                          *)
(*   ToSet(<<1,1,2>>) = {1,2}                                            *)
(*                                                                       *)
(* See: https://en.wikipedia.org/wiki/Image_(mathematics)                *)
(*************************************************************************)
ToSet(s) ==
  { s[i] : i \in DOMAIN s }

(**************************************************************************)
(* Convert a set to some sequence that contains all the elements of the   *)
(* set exactly once, and contains no other elements.                      *)
(**************************************************************************)
SetToSeq(S) == 
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

(**************************************************************************)
(* Convert the set S to a set containing all sequences containing the     *)
(* elements of S exactly once and no other elements.                      *)
(* Example:                                                               *)
(*    SetToSeqs({}), {<<>>}                                               *)
(*    SetToSeqs({"t","l"}) = {<<"t","l">>, <<"l","t">>}                   *) 
(**************************************************************************)
SetToSeqs(S) == 
  LET D == 1..Cardinality(S)
  IN { f \in [D -> S] : \A i,j \in D : i # j => f[i] # f[j] }

(**************************************************************************)
(* Convert a set to a sorted sequence that contains all the elements of   *)
(* the set exactly once, and contains no other elements.                  *)
(**************************************************************************)
SetToSortSeq(S, op(_,_)) ==
  SortSeq(SetToSeq(S), op)

(**************************************************************************)
(* Convert the set S to a set containing all k-permutations of elements   *)
(* of S for k \in 0..Cardinality(S).                                      *)
(* Example:                                                               *)
(*    SetToAllKPermutations({}) = {<<>>}                                  *)
(*    SetToAllKPermutations({"a"}) = {<<>>, <<"a">>}                      *)
(*    SetToAllKPermutations({"a","b"}) =                                  *)
(*                    {<<>>, <<"a">>, <<"b">>,<<"a","b">>, <<"b","a">>}   *)
(**************************************************************************)
SetToAllKPermutations(S) ==
  UNION { SetToSeqs(s) : s \in SUBSET S  }

(***************************************************************************)
(* TupleOf(s, 3) = s \X s \X s                                             *)
(***************************************************************************)
TupleOf(set, n) == 
  [1..n -> set]

(***************************************************************************)
(* All sequences up to length n with all elements in set.  Includes empty  *)
(* sequence.                                                               *)
(***************************************************************************)
SeqOf(set, n) == 
  UNION {[1..m -> set] : m \in 0..n}

(***************************************************************************)
(* An alias for SeqOf to make the connection to Sequences!Seq, which is    *)
(* the unbounded version of BoundedSeq.                                    *)
(***************************************************************************)
BoundedSeq(S, n) ==
  SeqOf(S, n)

-----------------------------------------------------------------------------

(**************************************************************************)
(* TRUE iff the element e \in ToSet(s).                                   *)
(**************************************************************************)
Contains(s, e) ==
  \E i \in 1..Len(s) : s[i] = e

(**************************************************************************)
(* Reverse the given sequence s:  Let l be Len(s) (length of s).          *)
(* Equals a sequence s.t. << S[l], S[l-1], ..., S[1]>>                    *)
(**************************************************************************)
Reverse(s) ==
  [ i \in 1..Len(s) |-> s[(Len(s) - i) + 1] ]

(************************************************************************)
(* The sequence s with e removed or s iff e \notin Range(s)             *)
(************************************************************************)
Remove(s, e) ==
    SelectSeq(s, LAMBDA t: t # e)

(*************************************************************************)
(* Equals the sequence s except that all occurrences of element old are  *)
(* replaced with the element new.                                        *)
(*************************************************************************)
ReplaceAll(s, old, new) ==
  [i \in 1 .. Len(s) |-> IF s[i] = old THEN new ELSE s[i]]

-----------------------------------------------------------------------------

(*************************************************************************)
(* Selects the index of the first element such that Test(seq[i]) is true *)
(* Equals 0 if Test(seq[i]) is FALSE for all elements.                   *)
(*************************************************************************)
SelectInSeq(seq, Test(_)) ==
  LET I == { i \in 1..Len(seq) : Test(seq[i]) }
  IN IF I # {} THEN Min(I) ELSE 0

(*************************************************************************)
(* Selects the index of the first element in seq such that Test(seq[i])  *)
(* is TRUE for this elements in from..to.  Equals 0 if Test(seq[i]) is   *)
(* FALSE for all elements.                                               *)
(*************************************************************************)
SelectInSubSeq(seq, from, to, Test(_)) ==
  SelectInSeq(SubSeq(seq, from, to), Test)

(*************************************************************************)
(* Selects the index of the last element such that Test(seq[i]) is true  *)
(* Equals 0 if Test(seq[i]) is FALSE for all elements.                   *)
(*************************************************************************)
SelectLastInSeq(seq, Test(_)) ==
  LET I == { i \in 1..Len(seq) : Test(seq[i]) }
  IN IF I # {} THEN Max(I) ELSE 0

(*************************************************************************)
(* Selects the index of the last element in seq such that Test(seq[i])   *)
(* is TRUE for this elements in from..to.  Equals 0 if Test(seq[i]) is   *)
(* FALSE for all elements.                                               *)
(*************************************************************************)
SelectLastInSubSeq(seq, from, to, Test(_)) ==
  SelectLastInSeq(SubSeq(seq, from, to), Test)

-----------------------------------------------------------------------------

\* The operators below up to including IsStrictSuffix have been extracted 
\* from the TLAPS module SequencesTheorems.tla as of 10/14/2019.  The original
\* comments have been partially rewritten.

(**************************************************************************)
(* Inserts element e at the position i moving the original element to i+1 *)
(* and so on.  In other words, a sequence t s.t.:                         *)
(*   /\ Len(t) = Len(s) + 1                                               *)
(*   /\ t[i] = e                                                          *)
(*   /\ \A j \in 1..(i - 1): t[j] = s[j]                                  *)
(*   /\ \A k \in (i + 1)..Len(s): t[k + 1] = s[k]                         *)
(**************************************************************************)
InsertAt(s, i, e) ==
  SubSeq(s, 1, i-1) \o <<e>> \o SubSeq(s, i, Len(s))

(**************************************************************************)
(* Replaces the element at position i with the element e.                 *)
(**************************************************************************)
ReplaceAt(s, i, e) ==
  [s EXCEPT ![i] = e]
  
(**************************************************************************)
(* Replaces the element at position i shortening the length of s by one.  *)
(**************************************************************************)
RemoveAt(s, i) == 
  SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

(************************************************************************)
(* The sequence s with the first occurrence of e removed or s           *)
(* iff e \notin Range(s)                                                *)
(************************************************************************)
RemoveFirst(s, e) ==
    IF \E i \in 1..Len(s): s[i] = e
    THEN RemoveAt(s, SelectInSeq(s, LAMBDA v: v = e))
    ELSE s

(************************************************************************)
(* The sequence s with the first element removed s.t. Test(e) or s      *)
(* iff e \notin Range(s)                                                *)
(************************************************************************)
RemoveFirstMatch(s, Test(_)) ==
    IF \E i \in 1..Len(s): Test(s[i])
    THEN RemoveAt(s, SelectInSeq(s, Test))
    ELSE s

-----------------------------------------------------------------------------

(************************************************************************)
(* Cons prepends an element at the beginning of a sequence.             *)
(************************************************************************)
Cons(elt, seq) == 
    <<elt>> \o seq

(************************************************************************)
(* Reverses the operands of Sequences!Append for better compatibility   *)
(* with FoldFunction below.                                             *)
(* Example:                                                             *)
(*  FoldSeq(LAMBDA x,y: {x} \cup y, {}, <<1,2,1>>) = Range(<<1,2,1>>)   *)
(************************************************************************)
Snoc(elt, seq) == 
    Append(seq, elt)

(**************************************************************************)
(* The sequence formed by removing its last element.                      *)
(**************************************************************************)
Front(s) == 
  SubSeq(s, 1, Len(s)-1)

(**************************************************************************)
(* The last element of the sequence.                                      *)
(**************************************************************************)
Last(s) ==
  s[Len(s)]

-----------------------------------------------------------------------------

(**************************************************************************)
(* TRUE iff the sequence s is a prefix of the sequence t, s.t.            *)
(* \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists      *)
(* a suffix u that with s prepended equals t.                             *)
(**************************************************************************)
IsPrefix(s, t) ==
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))

(**************************************************************************)
(* TRUE iff the sequence s is a prefix of the sequence t and s # t        *)
(**************************************************************************)
IsStrictPrefix(s,t) ==
  IsPrefix(s, t) /\ s # t

(**************************************************************************)
(* TRUE iff the sequence s is a suffix of the sequence t, s.t.            *)
(* \E u \in Seq(Range(t)) : t = u \o s. In other words, there exists a    *)
(* prefix that with s appended equals t.                                  *)
(**************************************************************************)
IsSuffix(s, t) ==
  IsPrefix(Reverse(s), Reverse(t))

(**************************************************************************)
(* TRUE iff the sequence s is a suffix of the sequence t and s # t        *)
(**************************************************************************)
IsStrictSuffix(s, t) ==
  IsSuffix(s,t) /\ s # t
  
-----------------------------------------------------------------------------

(**************************************************************************)
(* The set of prefixes of the sequence s, including the empty sequence.   *)
(**************************************************************************)
Prefixes(s) ==
  { SubSeq(s, 1, l) : l \in 0..Len(s) } \* 0.. for <<>>

(**************************************************************************)
(* The set of all sequences that are prefixes of the set of sequences S.  *)
(**************************************************************************)
CommonPrefixes(S) ==
  LET P == UNION { Prefixes(seq) : seq \in S }
  IN { prefix \in P : \A t \in S: IsPrefix(prefix, t) }

(**************************************************************************)
(* The longest common prefix of the sequences in the set S.               *)
(**************************************************************************)
LongestCommonPrefix(S) ==
  CHOOSE longest \in CommonPrefixes(S):  \* there can only be one LCP => CHOOSE
          \A other \in CommonPrefixes(S):
              Len(other) <= Len(longest)

(**************************************************************************)
(* The set of suffixes of the sequence s, including the empty sequence.   *)
(**************************************************************************)
Suffixes(s) ==
  { SubSeq(s, l, Len(s)) : l \in 1..Len(s) } \cup {<<>>}

-----------------------------------------------------------------------------

(***************************************************************************)
(*   Range(a % b) = 0..b-1, but DOMAIN seq = 1..Len(seq).                  *)
(*   So to do modular arithmetic on sequences we need to                   *)
(*   map 0 to b.                                                           *)
(***************************************************************************)
SeqMod(a, b) == 
  IF a % b = 0 THEN b ELSE a % b


(***************************************************************************)
(* An alias of FoldFunction that op on all elements of seq an arbitrary    *)
(* order. The resulting function is:                                       *)
(*    op(f[i],op(f[j], ..., op(f[k],base) ...))                            *)
(*                                                                         *)
(* op must be associative and commutative, because we can not assume a     *)
(* particular ordering of i, j, and k                                      *)
(*                                                                         *)
(* Example:                                                                *)
(*  FoldSeq(LAMBDA x,y: {x} \cup y, {}, <<1,2,1>>) = Range(<<1,2,1>>)      *)
(***************************************************************************)
FoldSeq(op(_, _), base, seq) == 
  FoldFunction(op, base, seq)

(***************************************************************************)
(* FoldLeft folds op on all elements of seq from left to right, starting   *)
(* with the first element and base. The resulting function is:             *)
(*    op(op(...op(base,f[0]), ...f[n-1]), f[n])                            *)
(*                                                                         *)
(*                                                                         *)
(* Example:                                                                *)
(*    LET cons(x,y) == <<x,y>>                                             *)
(*    IN FoldLeft(cons, 0, <<3,1,2>>) = << << <<0,3>>, 1>>, 2>>            *)
(***************************************************************************)
FoldLeft(op(_, _), base, seq) == 
  MapThenFoldSet(LAMBDA x,y : op(y,x), base,
                 LAMBDA i : seq[i],
                 LAMBDA S : Max(S),
                 DOMAIN seq)

(***************************************************************************)
(* FoldRight folds op on all elements of seq from right to left, starting  *)
(* with the last element and base. The resulting function is:              *)
(*    op(f[0],op(f[1], ..., op(f[n],base) ...))                            *)
(*                                                                         *)
(*                                                                         *)
(* Example:                                                                *)
(*    LET cons(x,y) == <<x,y>>                                             *)
(*    IN FoldRight(cons, <<3,1,2>>, 0 ) = << 3, << 1, <<2,0>> >> >>        *)
(***************************************************************************)
FoldRight(op(_, _), seq, base) == 
  MapThenFoldSet(op, base,
                 LAMBDA i : seq[i],
                 LAMBDA S : Min(S),
                 DOMAIN seq)

(***************************************************************************)
(* FoldLeftDomain folds op on the domain of seq, i.e., the seq's indices,  *)
(* starting at the lowest index.                                           *) 
(***************************************************************************)
FoldLeftDomain(op(_, _), base, seq) == 
  FoldLeft(op, base, [i \in DOMAIN seq |-> i])

(***************************************************************************)
(* FoldRightDomain folds op on the domain of seq, i.e., the seq's indices, *)
(* starting at the highest index.                                          *)
(***************************************************************************)
FoldRightDomain(op(_, _), seq, base) == 
  FoldRight(op, [i \in DOMAIN seq |-> i], base)

-----------------------------------------------------------------------------

(**************************************************************************)
(* A sequence of all elements from all sequences in the sequence  seqs  . *)
(*                                                                        *)
(* Examples:                                                              *)
(*                                                                        *)
(*  FlattenSeq(<< <<1,2>>, <<1>> >>) = << 1, 2, 1 >>                      *)
(*  FlattenSeq(<< <<"a">>, <<"b">> >>) = <<"a", "b">>                     *)
(*  FlattenSeq(<< "a", "b" >>) = "ab"                                     *)
(**************************************************************************)
FlattenSeq(seqs) ==
  IF Len(seqs) = 0 THEN seqs ELSE
    \* Not via  FoldSeq(\o, <<>>, seqs)  here to support strings with TLC.
    LET flatten[i \in 1..Len(seqs)] ==
        IF i = 1 THEN seqs[i] ELSE flatten[i-1] \o seqs[i]
    IN flatten[Len(seqs)]

(**************************************************************************)
(* A sequence of pairs where the i-th pair is formed from the i-th        *)
(* element of s and the i-th element of t. The length of the result       *)
(* sequence is the minimum of the lengths of s and t.                     *)
(*                                                                        *)
(* Examples:                                                              *)
(*                                                                        *)
(*  Zip(<< >>, << >>) = << >>                                             *)
(*  Zip(<<"a">>, <<"b">>) = << <<"a", "b">> >>                            *)
(*  Zip(<<1, 3>>, <<2, 4>>) = <<<<1, 2>>, <<3, 4>>>>                      *)
(*  FlattenSeq(Zip(<<1, 3>>, <<2, 4>>)) = <<1, 2, 3, 4>>>>                *)
(*  Zip(<< >>, <<1, 2, 3>>) = << >>                                       *)
(*  Zip(<<"a", "b", "c">>, <<1>>) = << <<"a", 1>> >>                      *)
(**************************************************************************)
Zip(s, t) ==
  LET l == IF Len(s) <= Len(t) THEN Len(s) ELSE Len(t)
  IN  [ i \in 1 .. l |-> <<s[i], t[i] >> ]

(**************************************************************************)
(* A sequence where the i-th tuple contains the i-th element of  s  and   *)
(*   t  in this order.  Not defined for  Len(s) # Len(t)                  *)
(*                                                                        *)
(* Examples:                                                              *)
(*                                                                        *)
(*  Interleave(<< >>, << >>) = << >>                                      *)
(*  Interleave(<<"a">>, <<"b">>) = <<"a", "b">>                           *)
(*  Interleave(<<1,3>>, <<2,4>>) = <<<<1>>, <<2>>, <<3>>, <<4>>>>         *)
(*  FlattenSeq(Interleave(<<1,3>>,<<2,4>>)) = <<1, 2, 3, 4>>              *)
(**************************************************************************)
Interleave(s, t) ==
  CASE Len(s) = Len(t) /\ Len(s) > 0 ->
        LET u[ i \in 1..Len(s) ] == 
                IF i = 1 THEN << <<s[i]>> >> \o << <<t[i]>> >>
                ELSE u[i-1] \o << <<s[i]>> >> \o << <<t[i]>> >>
        IN Last(u)
    \* error "Interleave: sequences must have same length"
    [] Len(s) = Len(t) /\ Len(s) = 0 -> << <<>>, <<>> >>

(**************************************************************************)
(* The set of all subsequences of the sequence  s  .  Note that the empty *)
(* sequence  <<>>  is defined to be a subsequence of any sequence.        *)
(**************************************************************************)
SubSeqs(s) ==
  { SubSeq(s, i+1, j) : i, j \in 0..Len(s) }

(**************************************************************************)
(* SubSeqs(s)                                                             *)
(*      \cup                                                              *)
(*         { subsequences of s, with arbitrarily many elts removed }      *)
(*                                                                        *)
(* Example:                                                               *)
(*  AllSubSeqs(<<1,2,3,4>>) =                                             *)
(*       {<<>>, <<1>>, <<2>>, <<3>>, <<4>>,                               *)
(*        <<1, 2>>, <<1, 3>>, <<1, 4>>,                                   *)
(*        <<2, 3>>, <<2, 4>>, <<3, 4>>,                                   *)
(*        <<1, 2, 3>>, <<1, 2, 4>>, <<1, 3, 4>>, <<2, 3, 4>>,             *)
(*        <<1, 2, 3, 4>>}                                                 *)
(**************************************************************************)
AllSubSeqs(s) ==
  { FoldFunction(Snoc, <<>>, [ i \in D |-> s[i] ]) : D \in SUBSET DOMAIN s }

(**************************************************************************)
(* The (1-based) index of the beginning of the subsequence  s  of the     *)
(* sequence  t  .  If  s  appears in  t  multiple times, this equals the  *)
(* lowest index.                                                          *)
(* For example:  IndexFirstSubSeq(<<1>>, <<1,1,1>>) = 1                   *)
(**************************************************************************)
IndexFirstSubSeq(s, t) ==
  LET last == CHOOSE i \in 0..Len(t) :
                /\ s \in SubSeqs(SubSeq(t, 1, i))
                /\ \A j \in 0..i-1 : s \notin SubSeqs(SubSeq(t, 1, j))
  IN last - (Len(s) - 1)

(**************************************************************************)
(* The sequence  t  with its subsequence  s  at position  i  replaced by  *)
(* the sequence  r  .                                                     *)
(**************************************************************************)
ReplaceSubSeqAt(i, r, s, t) ==
  LET prefix == SubSeq(t, 1, i - 1)
      suffix == SubSeq(t, i + Len(s), Len(t))
  IN prefix \o r \o suffix 

(**************************************************************************)
(* The sequence  t  with its subsequence  s  replaced by the sequence  r  *)
(**************************************************************************)
ReplaceFirstSubSeq(r, s, t) ==
  IF s \in SubSeqs(t)
  THEN ReplaceSubSeqAt(IndexFirstSubSeq(s, t), r, s, t)
  ELSE t

(**************************************************************************)
(* The sequence  t  with all subsequences  s  replaced by the sequence  r *)
(* Overlapping replacements are disambiguated by choosing the occurrence  *)
(* closer to the beginning of the sequence.                               *)
(*                                                                        *)
(* Examples:                                                              *)
(*                                                                        *)
(*  ReplaceAllSubSeqs(<<>>,<<>>,<<>>) = <<>>                              *)
(*  ReplaceAllSubSeqs(<<4>>,<<>>,<<>>) = <<4>>                            *)
(*  ReplaceAllSubSeqs(<<2>>,<<3>>,<<1,3>>) = <<1,2>>                      *)
(*  ReplaceAllSubSeqs(<<2,2>>,<<1,1>>,<<1,1,1>>) = <<2,2,1>>              *)
(**************************************************************************)
ReplaceAllSubSeqs(r, s, t) ==
  CASE s = t -> r
    [] r = s -> t  \* TLC optimization
    [] s # t /\ Len(s) = 0 ->
        LET z == Interleave([i \in 1..Len(t) |-> r], [i \in 1..Len(t) |-> <<t[i]>>])
        IN FlattenSeq(FlattenSeq(z))
    [] s # t /\ Len(s) > 0 /\ s \in SubSeqs(t) ->
        \* Not defined recursively to avoid infinite loops.
        LET match(f) == { i \in 1..Len(f) : s = f[i] }
            comp(p, q) == \A i \in 1..Len(p) : p[i] <= q[i]
            \* TODO: Replace with Seq(Seq(Range(t))) once *total* Java module
            \*       override in place. The current override handles only the
            \*       case where the parameters are strings (hence Range("abc") 
            \*       not a problem with TLC).
            R == BoundedSeq(BoundedSeq(Range(t), Len(t)), Len(t))
            \* A) Matches the input t.
            S == { f \in R : FlattenSeq(f) = t }
            \* B) Has the max number of matches...
            T == { f \in S : \A g \in S : 
                    Cardinality(match(g)) <= Cardinality(match(f)) }
            \* C) ...of min (leftmost) matches.
            u == CHOOSE f \in T : 
                    \A g \in T : comp(
                        SetToSortSeq(match(f), <), SetToSortSeq(match(g), <))
        IN FlattenSeq([i \in 1..Len(u) |-> IF s = u[i] THEN r ELSE u[i]])
    [] OTHER -> t

=============================================================================
