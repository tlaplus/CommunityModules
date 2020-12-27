------------------------ MODULE SequencesExtTheorems ------------------------
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE Functions

LEMMA EmptySingletonIsInjective ==
  /\ IsInjective(<< >>)
  /\ \A e : IsInjective(<< e >>)

LEMMA ConcatInjectiveSeq ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsInjective(s \o t) <=> 
         IsInjective(s) /\ IsInjective(t) /\ Range(s) \cap Range(t) = {}

LEMMA AppendInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  IsInjective(Append(seq,e)) <=> IsInjective(seq) /\ e \notin Range(seq)

LEMMA TailInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), IsInjective(seq), seq # << >>
  PROVE  /\ IsInjective(Tail(seq))
         /\ Range(Tail(seq)) = Range(seq) \ {Head(seq)}

LEMMA FrontInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), IsInjective(seq), seq # << >>
  PROVE  /\ IsInjective(Front(seq))
         /\ Range(Front(seq)) = Range(seq) \ {Last(seq)}

=============================================================================
\* Modification History
\* Last modified Sun Dec 27 09:34:35 CET 2020 by merz
\* Last modified Thu Feb 27 11:38:41 PST 2020 by markus
\* Created Tue Feb 25 20:49:08 PST 2020 by markus
