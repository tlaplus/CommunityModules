---- CONFIG FiniteSetsExtTests ----
INIT Init
NEXT Next
=====

------------------------- MODULE FiniteSetsExtTests -------------------------
EXTENDS Integers, TLC, TLCExt, FiniteSets, FiniteSetsExt

ASSUME LET S == {"a","b","c","c"}
       IN Quantify(S, LAMBDA s: s = "c") = Cardinality({s \in S : s = "c"})

ASSUME \A S \in SUBSET {"a","b","c","c"} :
		  Quantify(S, LAMBDA s: s = "c") = Cardinality({s \in S : s = "c"})

ASSUME \A S \in SUBSET {"a","b","c","c"} :
		  Quantify(S, LAMBDA s: FALSE) = Cardinality({s \in S : FALSE})

ASSUME LET S == 1..10
       IN Quantify(S, LAMBDA s: s = 3) = Cardinality({s \in S : s = 3})

(******************************************************************************) 
(* Test that Quantify handles sets that exceeds TLC's maxSetSize, which  *)
(* implies that no (intermediate) set is created.                             *)
(******************************************************************************) 
ASSUME LET S == 1..2000000
       IN Quantify(S, LAMBDA s: TRUE) = Cardinality(S)

-----------------------------------------------------------------------------

ASSUME LET S == {"a","b","c","c"} \* Make sure value normalization works.
       IN \A k \in -1..Cardinality(S) + 1: 
             kSubset(k, S) = {s \in SUBSET S : Cardinality(s) = k}

ASSUME LET S == {"a","b","c","c"} \* Make sure value normalization works.
       IN kSubset(-1, S) = {} /\ kSubset(4, S) = {}
  
\* The commented variant takes my computer ~30 seconds, whereas the kSubset
\* variant finishes in under 1s.  
\*ASSUME LET S == 1..27
\*       IN {s \in SUBSET S : Cardinality(s) = Cardinality(S)} = {S}
ASSUME LET S == 1..27
       IN kSubset(Cardinality(S), S) = {S}

-----------------------------------------------------------------------------

ASSUME ChooseUnique({2, 3, 4, 5}, LAMBDA x : x % 3 = 1) = 4

ASSUME AssertError(
           "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 96, col 26 to line 97, col 64 of module FiniteSetsExt", 
           ChooseUnique({2, 3, 4, 5}, LAMBDA x : TRUE))

ASSUME AssertError(
           "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 96, col 26 to line 97, col 64 of module FiniteSetsExt", 
           ChooseUnique({}, LAMBDA x : TRUE))

ASSUME AssertError(
           "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 96, col 26 to line 97, col 64 of module FiniteSetsExt", 
           ChooseUnique({2, 3, 4, 5}, LAMBDA x : FALSE))

-----------------------------------------------------------------------------

(* TLC won't evaluate the assumes above if a there is no behavior *)
(* spec. The config above is another artifact of this.            *)                              
\*VARIABLE x
\*
\*Init == FALSE /\ x = 0
\*
\*Next == FALSE /\ x' = x

=============================================================================
