--------------------- MODULE SequenceExtTheorems_proofs ---------------------
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE Functions
LOCAL INSTANCE TLAPS

LEMMA AppendTransitivityIsInjective \* With TLAPS 1.4.4+ (3ed0cde)
     == ASSUME NEW S, NEW seq \in Seq(S),
               IsInjective(seq),
               NEW elt \in S,
               elt \notin Range(seq)
        PROVE IsInjective(Append(seq, elt))
BY DEF IsInjective, Range

LEMMA TailTransitivityIsInjective \* With TLAPS 1.4.3
     == ASSUME NEW S, NEW seq \in Seq(S),
               seq # <<>>,
               IsInjective(seq)
        PROVE IsInjective(Tail(seq))
  <1> DEFINE ts == Tail(seq)
  <1>1. IsInjective(ts) 
    <2> SUFFICES ASSUME NEW i \in DOMAIN ts, NEW j \in DOMAIN ts,
                        ts[i] = ts[j]
                 PROVE  i = j
      BY DEF IsInjective
    <2>1. ts[i] = seq[i + 1] /\ ts[j] = seq[j + 1] 
      BY SMT
    <2>2. 1..Len(ts) = 1..Len(seq)-1
      BY SMT
    <2>3. 1..Len(ts) \subseteq 1..Len(seq)
      BY SMT
    <2>4. DOMAIN ts = 1..Len(seq)-1
      BY SMT
    <2>5. DOMAIN seq = 1..Len(seq)
      BY SMT
    <2>6. \A r, s \in 1..Len(seq): (seq[r] = seq[s]) => (r = s)
      BY Isa, <2>5 DEF IsInjective
    <2>7. seq \in [1..Len(seq) -> Range(seq)]
      BY Isa, <2>5 DEF Range
    <2>8. DOMAIN ts \subseteq DOMAIN seq
      BY Isa, <2>2, <2>3, <2>4, <2>7
    <2>9. QED BY <2>1, <2>2, <2>3, <2>5, <2>6, <2>7, <2>8 DEF IsInjective
  <1>2. QED BY <1>1

=============================================================================
\* Modification History
\* Last modified Thu Feb 27 11:44:49 PST 2020 by markus
\* Created Thu Feb 27 11:27:48 PST 2020 by markus
