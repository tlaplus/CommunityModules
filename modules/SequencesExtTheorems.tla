----------------------- MODULE SequencesExtTheorems ------------------------
(**************************************************************************)
(* This module contains theorems about the operators on sequences defined *)
(* in module SequencesExt.                                                *)
(* The proofs are given in module SequencesExtTheorems_proofs.            *)
(**************************************************************************)
EXTENDS Sequences, SequencesExt, Functions, Integers, WellFoundedInduction

(***************************************************************************)
(* Theorems about Cons.                                                    *)
(* Cons(elt, seq) == <<elt>> \o seq                                        *)
(***************************************************************************)

THEOREM ConsProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE /\ Cons(elt, seq) \in Seq(S)
        /\ Cons(elt, seq) # <<>>
        /\ Len(Cons(elt, seq)) = Len(seq)+1
        /\ Head(Cons(elt, seq)) = elt
        /\ Tail(Cons(elt, seq)) = seq
        /\ Cons(elt, seq)[1] = elt
        /\ \A i \in 1 .. Len(seq) : Cons(elt, seq)[i+1] = seq[i]
        /\ \A i \in 2 .. Len(seq)+1 : Cons(elt, seq)[i] = seq[i-1]

THEOREM ConsEmpty ==
  \A x : Cons(x, << >>) = << x >>

THEOREM ConsHeadTail ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Cons(Head(seq), Tail(seq)) = seq

THEOREM ConsAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW x \in S, NEW y \in S
  PROVE  Cons(x, Append(seq, y)) = Append(Cons(x,seq), y)

THEOREM ConsInjective ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW f \in S, NEW t \in Seq(S)
  PROVE  Cons(e,s) = Cons(f,t) <=> e = f /\ s = t

THEOREM SequencesInductionCons ==
  ASSUME NEW P(_), NEW S,
         P(<< >>),
         \A s \in Seq(S), e \in S : P(s) => P(Cons(e,s))
  PROVE \A seq \in Seq(S) : P(seq)

(***************************************************************************)
(* Theorems about InsertAt and RemoveAt.                                   *)
(* InsertAt(seq,i,elt) ==                                                  *)
(*   SubSeq(seq, 1, i-1) \o <<elt>> \o SubSeq(seq, i, Len(seq))            *)
(* RemoveAt(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))   *)
(***************************************************************************)

THEOREM InsertAtProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq)+1, NEW elt \in S
  PROVE  /\ InsertAt(seq,i,elt) \in Seq(S)
         /\ Len(InsertAt(seq,i,elt)) = Len(seq)+1
         /\ \A j \in 1 .. Len(seq)+1 : InsertAt(seq,i,elt)[j] =
                     IF j<i THEN seq[j]
                     ELSE IF j=i THEN elt
                     ELSE seq[j-1]

THEOREM RemoveAtProperties ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE  /\ RemoveAt(seq,i) \in Seq(S)
          /\ Len(RemoveAt(seq,i)) = Len(seq) - 1
          /\ \A j \in 1 .. Len(seq)-1 : RemoveAt(seq,i)[j] = IF j<i THEN seq[j] ELSE seq[j+1]

(***************************************************************************)
(* Theorems about Front and Last.                                          *)
(* Front(seq) == SubSeq(seq, 1, Len(seq)-1)                                *)
(* Last(seq) == seq[Len(seq)]                                              *)
(***************************************************************************)

THEOREM FrontProperties ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Front(seq) \in Seq(S)
         /\ Len(Front(seq)) = IF seq = << >> THEN 0 ELSE Len(seq)-1
         /\ \A i \in 1 .. Len(seq)-1 : Front(seq)[i] = seq[i]

THEOREM FrontOfEmpty == Front(<< >>) = << >>

THEOREM LastProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  /\ Last(seq) \in S
         /\ Append(Front(seq), Last(seq)) = seq

THEOREM FrontLastOfSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ Front(SubSeq(seq,m,n)) = SubSeq(seq, m, n-1)
         /\ Last(SubSeq(seq,m,n)) = seq[n]

THEOREM FrontLastAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  /\ Front(Append(seq, e)) = seq
         /\ Last(Append(seq, e)) = e

LEMMA FrontInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), IsInjective(seq), seq # << >>
  PROVE  /\ IsInjective(Front(seq))
         /\ Range(Front(seq)) = Range(seq) \ {Last(seq)}

THEOREM SequencesInductionFront ==
  ASSUME NEW S,  NEW P(_),
         P(<< >>),
         \A s \in Seq(S) : (s # << >>) /\ P(Front(s)) => P(s)
  PROVE  \A s \in Seq(S) : P(s)

(***************************************************************************)
(* Theorems about Reverse.                                                 *)
(* Reverse(seq) == [j \in 1 .. Len(seq) |-> seq[Len(seq)-j+1] ]            *)
(***************************************************************************)

THEOREM ReverseProperties ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Reverse(seq) \in Seq(S)
         /\ Len(Reverse(seq)) = Len(seq)
         /\ Reverse(Reverse(seq)) = seq

THEOREM ReverseEmpty == Reverse(<< >>) = << >>

THEOREM ReverseEqual ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), Reverse(s) = Reverse(t)
  PROVE  s = t

THEOREM ReverseEmptyIffEmpty ==
  ASSUME NEW S, NEW seq \in Seq(S), Reverse(seq) = <<>>
  PROVE  seq = <<>>

THEOREM ReverseConcat ==
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Reverse(s1 \o s2) = Reverse(s2) \o Reverse(s1)

THEOREM ReverseAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Append(seq,e)) = Cons(e, Reverse(seq))

THEOREM ReverseCons ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Cons(e,seq)) = Append(Reverse(seq), e)

THEOREM ReverseSingleton == \A x : Reverse(<< x >>) = << x >>

THEOREM ReverseSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1..Len(seq), NEW n \in 1..Len(seq)
  PROVE  Reverse(SubSeq(seq, m , n)) = SubSeq(Reverse(seq), Len(seq)-n+1, Len(seq)-m+1)

THEOREM ReversePalindrome ==
  ASSUME NEW S, NEW seq \in Seq(S),
         Reverse(seq) = seq
  PROVE  Reverse(seq \o seq) = seq \o seq

THEOREM LastEqualsHeadReverse ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Last(seq) = Head(Reverse(seq))

THEOREM ReverseFrontEqualsTailReverse ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Reverse(Front(seq)) = Tail(Reverse(seq))

(* The range of the reverse sequence equals that of the original one. *)
THEOREM RangeReverse ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE /\ DOMAIN Reverse(seq) = DOMAIN seq
        /\ Range(Reverse(seq)) = Range(seq)

(***************************************************************************)
(* The following theorem gives three alternative characterizations of      *)
(* prefixes. It also implies that any prefix of a sequence t is at most    *)
(* as long as t.                                                           *)
(***************************************************************************)
THEOREM IsPrefixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsPrefix(s,t) <=> \E u \in Seq(S) : t = s \o u
         /\ IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))
         /\ IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = Restrict(t, DOMAIN s)

THEOREM IsStrictPrefixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsStrictPrefix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = s \o u
         /\ IsStrictPrefix(s,t) <=> Len(s) < Len(t) /\ s = SubSeq(t, 1, Len(s))
         /\ IsStrictPrefix(s,t) <=> Len(s) < Len(t) /\ s = Restrict(t, DOMAIN s)
         /\ IsStrictPrefix(s,t) <=> IsPrefix(s,t) /\ Len(s) < Len(t)

THEOREM IsPrefixElts ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW i \in 1 .. Len(s),
         IsPrefix(s,t)
  PROVE  s[i] = t[i]

THEOREM EmptyIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsPrefix(<<>>, s)
         /\ IsPrefix(s, <<>>) <=> s = <<>>
         /\ IsStrictPrefix(<<>>, s) <=> s # <<>>
         /\ ~ IsStrictPrefix(s, <<>>)

THEOREM IsPrefixConcat ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsPrefix(s, s \o t)

THEOREM IsStrictPrefixAppend ==
  ASSUME NEW S, NEW s \in Seq(S), NEW e \in S
  PROVE  IsStrictPrefix(s, Append(s,e))

THEOREM FrontIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsPrefix(Front(s), s)
         /\ s # <<>> => IsStrictPrefix(Front(s), s)

(***************************************************************************)
(* (Strict) prefixes on sequences form a (strict) partial order, and       *)
(* the strict ordering is well-founded.                                    *)
(***************************************************************************)
THEOREM IsPrefixPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : IsPrefix(s,s)
         /\ \A s,t \in Seq(S) : IsPrefix(s,t) /\ IsPrefix(t,s) => s = t
         /\ \A s,t,u \in Seq(S) : IsPrefix(s,t) /\ IsPrefix(t,u) => IsPrefix(s,u)

THEOREM ConcatIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
         IsPrefix(s \o t, u)
  PROVE  IsPrefix(s, u)

THEOREM ConcatIsPrefixCancel ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  /\ IsPrefix(s \o t, s \o u) <=> IsPrefix(t, u)

THEOREM ConsIsPrefixCancel ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsPrefix(Cons(e,s), Cons(e,t)) <=> IsPrefix(s,t)

THEOREM ConsIsPrefix ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW u \in Seq(S),
         IsPrefix(Cons(e,s), u)
  PROVE  /\ e = Head(u)
         /\ IsPrefix(s, Tail(u))

THEOREM IsStrictPrefixStrictPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : ~ IsStrictPrefix(s,s)
         /\ \A s,t \in Seq(S) : IsStrictPrefix(s,t) => ~ IsStrictPrefix(t,s)
         /\ \A s,t,u \in Seq(S) : IsStrictPrefix(s,t) /\ IsStrictPrefix(t,u) => IsStrictPrefix(s,u)

THEOREM IsStrictPrefixWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S))

THEOREM SeqStrictPrefixInduction ==
  ASSUME NEW P(_), NEW S,
         \A t \in Seq(S) : (\A s \in Seq(S) : IsStrictPrefix(s,t) => P(s)) => P(t)
  PROVE  \A s \in Seq(S) : P(s)

(***************************************************************************)
(* Similar theorems about suffixes.                                        *)
(***************************************************************************)

THEOREM IsSuffixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsSuffix(s,t) <=> \E u \in Seq(S) : t = u \o s
         /\ IsSuffix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))

THEOREM IsStrictSuffixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsStrictSuffix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = u \o s
         /\ IsStrictSuffix(s,t) <=> Len(s) < Len(t) /\ IsSuffix(s,t)
         /\ IsStrictSuffix(s,t) <=> Len(s) < Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
         /\ IsStrictSuffix(s,t) <=> IsStrictPrefix(Reverse(s), Reverse(t))

THEOREM IsSuffixElts ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW i \in 1 .. Len(s),
         IsSuffix(s,t)
  PROVE  s[i] = t[Len(t) - Len(s) + i]

THEOREM EmptyIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsSuffix(<<>>, s)
         /\ IsSuffix(s, <<>>) <=> s = <<>>
         /\ IsStrictSuffix(<<>>, s) <=> s # <<>>
         /\ ~ IsStrictSuffix(s, <<>>)

THEOREM IsSuffixConcat ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsSuffix(s, t \o s)

THEOREM IsStrictSuffixCons ==
  ASSUME NEW S, NEW s \in Seq(S), NEW e \in S
  PROVE  IsStrictSuffix(s, Cons(e,s))

THEOREM TailIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S), s # << >>
  PROVE  IsStrictSuffix(Tail(s), s)

THEOREM IsSuffixPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : IsSuffix(s,s)
         /\ \A s,t \in Seq(S) : IsSuffix(s,t) /\ IsSuffix(t,s) => s = t
         /\ \A s,t,u \in Seq(S) : IsSuffix(s,t) /\ IsSuffix(t,u) => IsSuffix(s,u)

THEOREM ConcatIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
         IsSuffix(s \o t, u)
  PROVE  IsSuffix(t, u)

THEOREM ConcatIsSuffixCancel ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  IsSuffix(s \o t, u \o t) <=> IsSuffix(s, u)

THEOREM AppendIsSuffixCancel ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsSuffix(Append(s,e), Append(t,e)) <=> IsSuffix(s,t)

THEOREM AppendIsSuffix ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW u \in Seq(S),
         IsSuffix(Append(s,e), u)
  PROVE  /\ e = Last(u)
         /\ IsSuffix(s, Front(u))

THEOREM IsStrictSuffixStrictPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : ~ IsStrictSuffix(s,s)
         /\ \A s,t \in Seq(S) : IsStrictSuffix(s,t) => ~ IsStrictSuffix(t,s)
         /\ \A s,t,u \in Seq(S) : IsStrictSuffix(s,t) /\ IsStrictSuffix(t,u) => IsStrictSuffix(s,u)

THEOREM IsStrictSuffixWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S))

THEOREM SeqStrictSuffixInduction ==
  ASSUME NEW P(_), NEW S,
         \A t \in Seq(S) : (\A s \in Seq(S) : IsStrictSuffix(s,t) => P(s)) => P(t)
  PROVE  \A s \in Seq(S) : P(s)

(***************************************************************************)
(* Since the (strict) prefix and suffix orderings on sequences are         *)
(* well-founded, they can be used for defining recursive functions.        *)
(* The operators OpDefinesFcn, WFInductiveDefines, and WFInductiveUnique   *)
(* are defined in module WellFoundedInduction.                             *)
(***************************************************************************)

StrictPrefixesDetermineDef(S, Def(_,_)) ==
   \A g,h : \A seq \in Seq(S) :
      (\A pre \in Seq(S) : IsStrictPrefix(pre,seq) => g[pre] = h[pre])
      => Def(g, seq) = Def(h, seq)

LEMMA StrictPrefixesDetermineDef_WFDefOn ==
  ASSUME NEW S, NEW Def(_,_), StrictPrefixesDetermineDef(S, Def)
  PROVE  WFDefOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S), Def)

THEOREM PrefixRecursiveSequenceFunctionUnique ==
  ASSUME NEW S, NEW Def(_,_), StrictPrefixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)

THEOREM PrefixRecursiveSequenceFunctionDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictPrefixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)

THEOREM PrefixRecursiveSequenceFunctionType ==
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T # {},
         StrictPrefixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         \A g \in [Seq(S) -> T], s \in Seq(S) : Def(g,s) \in T
  PROVE  f \in [Seq(S) -> T]

StrictSuffixesDetermineDef(S, Def(_,_)) ==
   \A g,h : \A seq \in Seq(S) :
      (\A suf \in Seq(S) : IsStrictSuffix(suf,seq) => g[suf] = h[suf])
      => Def(g, seq) = Def(h, seq)

LEMMA StrictSuffixesDetermineDef_WFDefOn ==
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFDefOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S), Def)

THEOREM SuffixRecursiveSequenceFunctionUnique ==
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)

THEOREM SuffixRecursiveSequenceFunctionDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictSuffixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)

THEOREM SuffixRecursiveSequenceFunctionType ==
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T # {},
         StrictSuffixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         \A g \in [Seq(S) -> T], s \in Seq(S) : Def(g,s) \in T
  PROVE  f \in [Seq(S) -> T]

(***************************************************************************)
(* The following theorems justify ``primitive recursive'' functions over   *)
(* sequences, with a base case for the empty sequence and recursion along  *)
(* either the Tail or the Front of a non-empty sequence.                   *)
(***************************************************************************)

TailInductiveDefHypothesis(f, S, f0, Def(_,_)) ==
  f = CHOOSE g : g = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(g[Tail(s)], s)]

TailInductiveDefConclusion(f, S, f0, Def(_,_)) ==
  f = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(f[Tail(s)], s)]

THEOREM TailInductiveDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0,
         TailInductiveDefHypothesis(f, S, f0, Def)
  PROVE  TailInductiveDefConclusion(f, S, f0, Def)

THEOREM TailInductiveDefType ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         TailInductiveDefConclusion(f, S, f0, Def),
         f0 \in T,
         \A v \in T, s \in Seq(S) : s # <<>> => Def(v,s) \in T
  PROVE  f \in [Seq(S) -> T]

FrontInductiveDefHypothesis(f, S, f0, Def(_,_)) ==
  f = CHOOSE g : g = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(g[Front(s)], s)]

FrontInductiveDefConclusion(f, S, f0, Def(_,_)) ==
  f = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(f[Front(s)], s)]

THEOREM FrontInductiveDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0,
         FrontInductiveDefHypothesis(f, S, f0, Def)
  PROVE  FrontInductiveDefConclusion(f, S, f0, Def)

THEOREM FrontInductiveDefType ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         FrontInductiveDefConclusion(f, S, f0, Def),
         f0 \in T,
         \A v \in T, s \in Seq(S) : s # <<>> => Def(v,s) \in T
  PROVE  f \in [Seq(S) -> T]

----------------------------------------------------------------------------

(**************************************************************************)
(* Recursive characterization of FoldLeft.                                *)
(**************************************************************************)
THEOREM FoldLeftRecursion ==
  ASSUME NEW op(_,_), NEW base, NEW S, NEW seq \in Seq(S)
  PROVE  FoldLeft(op, base, seq) = 
           IF seq = << >> THEN base 
           ELSE op(FoldLeft(op, base, Front(seq)), Last(seq))

THEOREM FoldLeftEmpty ==
  ASSUME NEW op(_,_), NEW base
  PROVE  FoldLeft(op, base, <<>>) = base

THEOREM FoldLeftNonempty ==
  ASSUME NEW op(_,_), NEW base, NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  FoldLeft(op, base, seq) = op(FoldLeft(op, base, Front(seq)), Last(seq))

(**************************************************************************)
(* Interaction of FoldLeft and Append.                                    *)
(**************************************************************************)
THEOREM FoldLeftAppend ==
    ASSUME NEW op(_,_), NEW base, NEW S, NEW seq \in Seq(S), NEW s \in S 
    PROVE  FoldLeft(op, base, Append(seq,s)) = op(FoldLeft(op, base, seq), s)

(**************************************************************************)
(* Type of FoldLeft.                                                      *)
(**************************************************************************)
THEOREM FoldLeftType ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, NEW seq \in Seq(Typ),
           \A t,u \in Typ : op(t,u) \in Typ 
    PROVE  FoldLeft(op, base, seq) \in Typ 

(**************************************************************************)
(* Recursive characterization of FoldRight.                               *)
(**************************************************************************)
THEOREM FoldRightRecursion ==
  ASSUME NEW op(_,_), NEW base, NEW S, NEW seq \in Seq(S)
  PROVE  FoldRight(op, seq, base) = 
           IF seq = << >> THEN base 
           ELSE op(Head(seq), FoldRight(op, Tail(seq), base))

THEOREM FoldRightEmpty ==
  ASSUME NEW op(_,_), NEW base
  PROVE  FoldRight(op, <<>>, base) = base

THEOREM FoldRightNonempty ==
  ASSUME NEW op(_,_), NEW base, NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  FoldRight(op, seq, base) = op(Head(seq), FoldRight(op, Tail(seq), base))

(**************************************************************************)
(* Interaction of FoldRight and Cons.                                     *)
(**************************************************************************)
THEOREM FoldRightCons ==
    ASSUME NEW op(_,_), NEW base, NEW S, NEW seq \in Seq(S), NEW s \in S 
    PROVE  FoldRight(op, Cons(s, seq), base) = op(s, FoldRight(op, seq, base))

(**************************************************************************)
(* Type of FoldRight.                                                     *)
(**************************************************************************)
THEOREM FoldRightType ==
    ASSUME NEW Typ, NEW op(_,_), NEW base \in Typ, NEW seq \in Seq(Typ),
           \A t,u \in Typ : op(t,u) \in Typ 
    PROVE  FoldRight(op, seq, base) \in Typ 

(**************************************************************************)
(* FoldLeftDomain and FoldRightDomain cannot be characterized recursively *)
(* in terms of the same operators, we reduce them to MapThenFoldSet.      *)
(**************************************************************************)
THEOREM FoldLeftDomainIsMFS ==
    ASSUME NEW op(_,_), NEW base, NEW S, NEW seq \in Seq(S)
    PROVE  FoldLeftDomain(op, base, seq) =
           MapThenFoldSet(LAMBDA x,y : op(y,x), base, 
                          LAMBDA i : i, LAMBDA T : Max(T), 1 .. Len(seq))

THEOREM FoldRightDomainIsMFS ==
    ASSUME NEW op(_,_), NEW base, NEW S, NEW seq \in Seq(S)
    PROVE  FoldRightDomain(op, seq, base) =
           MapThenFoldSet(op, base, 
                          LAMBDA i : i, LAMBDA T : Min(T), 1 .. Len(seq))

============================================================================
