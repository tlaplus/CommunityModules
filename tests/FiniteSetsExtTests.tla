---- CONFIG FiniteSetsExtTests ----
INIT Init
NEXT Next
=====

------------------------- MODULE FiniteSetsExtTests -------------------------
EXTENDS Integers, TLC, TLCExt, FiniteSets, FiniteSetsExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("FiniteSetsExtTests")

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

ASSUME {} \notin kSubset(1, {1,2,3})

ASSUME LET T == 1..3
       IN \A k \in (1..Cardinality(T)):
            /\ \A e \in { ss \in (SUBSET T) : Cardinality(ss) = k} :
                     e \in kSubset(k, T)
            /\ \A e \in { ss \in (SUBSET T) : Cardinality(ss) # k} :
                     e \notin kSubset(k, T)
                     
ASSUME LET T == {"a","b","c"}
           kSubsetPure(k, S) == { s \in SUBSET S : Cardinality(s) = k }
       IN \A k \in 1..Cardinality(T):
                /\ kSubset(k, T) = kSubsetPure(k, T)
                /\ kSubsetPure(k, T) = kSubset(k, T)
                
ASSUME LET T == {"a","b","c"}
       IN /\ kSubset(1, T) = {{"a"},{"b"},{"c"}}
          /\ kSubset(2, T) = {{"a","b"}, {"a","c"}, {"b","c"}}
          /\ kSubset(3, T) = {{"a","b","c"}}
          /\ {{"a"},{"b"},{"c"}} = kSubset(1, T)
          /\ {{"a","b"}, {"a","c"}, {"b","c"}} = kSubset(2, T)
          /\ {{"a","b","c"}} = kSubset(3, T)
                
ASSUME LET T == {"a","b","c"}
           kSubsetPure(k, S) == { s \in SUBSET S : Cardinality(s) = k }
       IN /\ {kSubset(k, T) : k \in 2..3} = {kSubsetPure(k, T) : k \in 2..3}
          /\ {kSubsetPure(k, T) : k \in 2..3} = {kSubset(k, T) : k \in 2..3}
          /\ {kSubsetPure(k, T) : k \in 2..3} = {kSubset(k, T) : k \in {3,2}}
          /\ (kSubset(2, T) \cup kSubset(3, T)) = (kSubsetPure(2, T) \cup kSubsetPure(3, T))
          /\ (kSubset(3, T) \cup kSubset(2, T)) = (kSubsetPure(2, T) \cup kSubsetPure(3, T))
          /\ (kSubset(1, T) \cup kSubset(2, T) \cup kSubset(3, T)) = (kSubsetPure(2, T) \cup kSubsetPure(3, T) \cup kSubsetPure(1, T))
          /\ (kSubset(3, T) \cup kSubset(1, T) \cup kSubset(2, T)) = (kSubsetPure(1, T) \cup kSubsetPure(2, T) \cup kSubsetPure(3, T) \cup kSubsetPure(3, T))
          /\ (kSubset(3, T) \cup kSubset(1, T) \cup kSubset(2, T)\cup kSubset(2, T)) = (kSubsetPure(1, T) \cup kSubsetPure(2, T) \cup kSubsetPure(3, T) \cup kSubsetPure(3, T))
          /\ (kSubset(3, T) \cup kSubset(1, T) \cup kSubset(2, T) \cup kSubset(0, T)) = (kSubsetPure(1, T) \cup kSubsetPure(2, T) \cup kSubsetPure(3, T) \cup kSubsetPure(0, T))

ASSUME LET T == 1..3
           kSubsetPure(k, S) == { s \in SUBSET S : Cardinality(s) = k }
       IN \A k \in 1..Cardinality(T):
                /\ ((SUBSET T) \subseteq kSubsetPure(k, T)) <=> ((SUBSET T) \subseteq kSubset(k, T))
                /\ kSubsetPure(k, T) \subseteq (SUBSET T) <=> kSubset(k, T) \subseteq (SUBSET T)

-----------------------------------------------------------------------------

ASSUME FoldSet(LAMBDA x,y : x + y, 0, 0 .. 10) = 55

-----------------------------------------------------------------------------

ASSUME ChooseUnique({2, 3, 4, 5}, LAMBDA x : x % 3 = 1) = 4

ASSUME AssertError(
           "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 124, col 26 to line 125, col 64 of module FiniteSetsExt", 
           ChooseUnique({2, 3, 4, 5}, LAMBDA x : TRUE))

ASSUME AssertError(
           "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 124, col 26 to line 125, col 64 of module FiniteSetsExt", 
           ChooseUnique({}, LAMBDA x : TRUE))

ASSUME AssertError(
           "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 124, col 26 to line 125, col 64 of module FiniteSetsExt", 
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
