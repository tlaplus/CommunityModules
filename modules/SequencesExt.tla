---------------------------- MODULE SequencesExt ----------------------------

LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

ToSet(s) ==
  (*************************************************************************)
  (* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
  (* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
  (*************************************************************************)
  { s[i] : i \in DOMAIN s }

IsInjective(s) == 
  (*************************************************************************)
  (* TRUE iff the sequence s contains no duplicates where two elements     *)
  (* a, b of s are defined to be duplicates iff a = b.  In other words,    *)
  (* Cardinality(ToSet(s)) = Len(s)                                        *)
  (*                                                                       *)
  (* This definition is overridden by TLC in the Java class SequencesExt.  *)
  (* The operator is overridden by the Java method with the same name.     *)
  (*************************************************************************)
  \A i, j \in DOMAIN s: (s[i] = s[j]) => (i = j)

SetToSeq(S) == 
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

=============================================================================
