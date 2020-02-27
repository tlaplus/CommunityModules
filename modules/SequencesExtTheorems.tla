------------------------ MODULE SequencesExtTheorems ------------------------
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE Functions

LEMMA AppendTransitivityIsInjective
     == ASSUME NEW S, NEW seq \in Seq(S),
               IsInjective(seq),
               NEW elt \in S,
               elt \notin Range(seq)
        PROVE IsInjective(Append(seq, elt))

LEMMA TailTransitivityIsInjective
     == ASSUME NEW S, NEW seq \in Seq(S),
               seq # <<>>,
               IsInjective(seq)
        PROVE IsInjective(Tail(seq))

=============================================================================
\* Modification History
\* Last modified Thu Feb 27 11:38:41 PST 2020 by markus
\* Created Tue Feb 25 20:49:08 PST 2020 by markus
