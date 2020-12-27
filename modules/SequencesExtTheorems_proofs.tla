--------------------- MODULE SequencesExtTheorems_proofs ---------------------
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE Functions
LOCAL INSTANCE TLAPS

LEMMA EmptySingletonIsInjective ==
  /\ IsInjective(<< >>)
  /\ \A e : IsInjective(<< e >>)
BY DEF IsInjective

LEMMA ConcatInjectiveSeq ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsInjective(s \o t) <=> 
         IsInjective(s) /\ IsInjective(t) /\ Range(s) \cap Range(t) = {}
<1>. DEFINE st == s \o t
<1>1. ASSUME IsInjective(st)  PROVE IsInjective(s)
  BY <1>1 DEF IsInjective
<1>2. ASSUME IsInjective(st)  PROVE IsInjective(t)
  <2>1. SUFFICES ASSUME NEW i \in DOMAIN t, NEW j \in DOMAIN t, t[i] = t[j]
                 PROVE  i = j
    BY DEF IsInjective
  <2>2. /\ i + Len(s) \in DOMAIN st
        /\ j + Len(s) \in DOMAIN st
        /\ st[i+Len(s)] = st[j + Len(s)]
    BY <2>1
  <2>. QED  BY <1>2, <2>2 DEF IsInjective
<1>3. ASSUME IsInjective(st), NEW e \in Range(s) \cap Range(t)
      PROVE  FALSE
  <2>1. PICK i \in DOMAIN s : s[i] = e
    BY <1>3 DEF Range
  <2>2. PICK j \in DOMAIN t : t[j] = e
    BY <1>3 DEF Range
  <2>3. /\ i \in DOMAIN st /\ st[i] = e
        /\ j+Len(s) \in DOMAIN st /\ st[j+Len(s)] = e
    BY <2>1, <2>2
  <2>. QED  BY <1>3, <2>3 DEF IsInjective
<1>4. ASSUME IsInjective(s), IsInjective(t), Range(s) \cap Range(t) = {}
      PROVE  IsInjective(st)
  BY <1>4 DEF IsInjective, Range
<1>. QED  BY <1>1, <1>2, <1>3, <1>4

LEMMA AppendInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  IsInjective(Append(seq,e)) <=> IsInjective(seq) /\ e \notin Range(seq)
<1>. DEFINE app == Append(seq,e)
<1>1. ASSUME IsInjective(app)
      PROVE  IsInjective(seq)
  BY <1>1 DEF IsInjective
<1>2. ASSUME IsInjective(app), e \in Range(seq)
      PROVE  FALSE
  <2>1. PICK i \in DOMAIN seq : seq[i] = e
    BY <1>2 DEF Range
  <2>2. app[i] = e /\ app[Len(seq)+1] = e
    BY <2>1
  <2>. QED
    BY <1>2, <2>2 DEF IsInjective
<1>3. ASSUME IsInjective(seq), e \notin Range(seq)
      PROVE  IsInjective(app)
  BY <1>3 DEF IsInjective, Range
<1>. QED  BY <1>1, <1>2, <1>3

LEMMA TailInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), IsInjective(seq), seq # << >>
  PROVE  /\ IsInjective(Tail(seq))
         /\ Range(Tail(seq)) = Range(seq) \ {Head(seq)}
<1>. DEFINE tl == Tail(seq)
<1>1. IsInjective(tl)
  BY DEF IsInjective
<1>2. ASSUME NEW e \in Range(tl)
      PROVE  e \in Range(seq) \ {Head(seq)}
  BY DEF Range, IsInjective
<1>3. ASSUME NEW e \in Range(seq) \ {Head(seq)}
      PROVE  e \in Range(tl)
  <2>1. PICK i \in 2 .. Len(seq) : seq[i] = e
    BY DEF Range
  <2>2. i-1 \in DOMAIN tl /\ tl[i-1] = e
    BY <2>1
  <2>. QED  BY <2>2, Zenon DEF Range
<1>. QED  BY <1>1, <1>2, <1>3

LEMMA FrontInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), IsInjective(seq), seq # << >>
  PROVE  /\ IsInjective(Front(seq))
         /\ Range(Front(seq)) = Range(seq) \ {Last(seq)}
<1>. DEFINE ft == Front(seq)
<1>1. IsInjective(ft)
  BY DEF IsInjective, Front
<1>2. ASSUME NEW e \in Range(ft)
      PROVE  e \in Range(seq) \ {Last(seq)}
  BY DEF Range, IsInjective, Front, Last
<1>3. ASSUME NEW e \in Range(seq) \ {Last(seq)}
      PROVE  e \in Range(ft)
  BY DEF Range, Front, Last
<1>. QED  BY <1>1, <1>2, <1>3

=============================================================================
\* Modification History
\* Last modified Sun Dec 27 09:33:28 CET 2020 by merz
\* Last modified Thu Feb 27 11:44:49 PST 2020 by markus
\* Created Thu Feb 27 11:27:48 PST 2020 by markus
