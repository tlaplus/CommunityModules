---------------------------- MODULE SequencesExt ----------------------------

LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

ToSet(s) ==
  (*************************************************************************)
  (* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
  (* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
  (*************************************************************************)
  { s[i] : i \in 1..Len(s) }

IsASet(s) == 
  (*************************************************************************)
  (* TRUE iff the sequence s contains no duplicates where two elements     *)
  (* a, b of s are defined to be duplicates iff a = b.  In other words,    *)
  (* Cardinality(ToSet(s)) = Len(s)                                        *)
  (*                                                                       *)
  (* This definition is overridden by TLC in the Java class                *)
  (* tlc2.module.SequencesExt. The operator is overridden by the Java      *)
  (* method with the same name.                                            *)
  (*************************************************************************)
  \A i,j \in 1..Len(s): i # j => s[i] # s[j]

=============================================================================
