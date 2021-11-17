--------------------------- MODULE FiniteSetsExt ---------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Functions
LOCAL INSTANCE Folds

FoldSet(op(_,_), base, set) ==
   (*************************************************************************)
   (* Fold op over the elements of set using base as starting value.        *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*         FoldSet(LAMBA x,y : x + y, 0, 0 .. 10) = 55                   *)
   (*************************************************************************)
   MapThenFoldSet(op, base, LAMBDA x : x, LAMBDA s : CHOOSE x \in s : TRUE, set)

Sum(set) ==
   (*************************************************************************)
   (* Calculate the sum of the elements in set.                             *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*         Sum(0 .. 10) = 55                                             *)
   (*************************************************************************)
   FoldSet(+, 0, set)

Product(set) ==
   (*************************************************************************)
   (* Calculuate the product of the elements in set.                        *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*         Product(1 .. 3) = 6                                           *)
   (*************************************************************************)
   FoldSet(LAMBDA x, y: x * y, 1, set)

ReduceSet(op(_, _), set, acc) == 
   (*************************************************************************)
   (* An alias for FoldSet. ReduceSet was used instead of FoldSet in        *)
   (* earlier versions of the community modules.                            *)
   (*************************************************************************)
   FoldSet(op, set, acc)


FlattenSet(S) ==
(******************************************************************************)
(* Starting from base, apply op to f(x), for all x \in S, in an arbitrary     *)
(* order. It is assumed that op is associative and commutative.               *)
(*                                                                            *)
(* Example:                                                                   *)
(*                                                                            *)
(*  FlattenSet({{1},{2}}) = {1,2}                                                *)
(******************************************************************************)
  FoldSet(LAMBDA x,y: x \cup y, {}, S) 

(***************************************************************************)
(* The symmetric difference of two sets.                                   *)
(*                                                                         *)
(* The symmetric difference of sets A and B is the set containing all      *)
(* elements that are present in either A or B but not in their             *)
(* intersection.                                                           *)
(***************************************************************************)
SymDiff(A, B) == (A \ B) \cup (B \ A)

-----------------------------------------------------------------------------

Quantify(S, P(_)) ==
   (*************************************************************************)
   (* Quantify the elements in S matching the predicate (LAMDBA) P.         *)
   (*                                                                       *)
   (* This operator is overridden by FiniteSetsExt#quantify whose           *)
   (* implementation does *not* enumerate the intermediate set! This is     *)
   (* the only advantage that Quantify(...) has over Cardinality(...).      *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*          Quantify(1..9, LAMBDA n : n % 2 = 0) = 4                     *)
   (*************************************************************************)
   Cardinality({s \in S : P(s)})

-----------------------------------------------------------------------------

kSubset(k, S) == 
   (*************************************************************************)
   (* A k-subset ks of a set S has Cardinality(ks) = k.  The number of      *)
   (* k-subsets of a set S with Cardinality(S) = n is given by the binomial *)
   (* coefficients n over k.  A set S with Cardinality(S) = n has 2^n       *)
   (* k-subsets.  \A k \notin 0..Cardinality(S): kSubset(k, S) = {}.        *)
   (*                                                                       *)
   (* This operator is overridden by FiniteSetsExt#kSubset whose            *)
   (* implementation, contrary to  { s \in SUBSET S : Cardinality(s) = k }, *)
   (* only enumerates the k-subsets of S and not all subsets.               *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*          kSubset(2, 1..3) = {{1,2},{2,3},{3,1}}                       *)
   (*************************************************************************)
   { s \in SUBSET S : Cardinality(s) = k }

-----------------------------------------------------------------------------

(***************************************************************************)
(* We define Max(S) and Min(S) to be the maximum and minimum,              *)
(* respectively, of a finite, non-empty set S of integers.                 *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

-----------------------------------------------------------------------------

(***************************************************************************) 
(* Compute all sets that contain one element from each of the input sets:  *)
(*                                                                         *)
(* Example:                                                                *)
(*          Choices({{1,2}, {2,3}, {5}}) =                                 *)
(*                         {{2, 5}, {1, 2, 5}, {1, 3, 5}, {2, 3, 5}}       *)
(***************************************************************************) 
Choices(Sets) == LET ChoiceFunction(Ts) == { f \in [Ts -> UNION Ts] : 
                                               \A T \in Ts : f[T] \in T }
                 IN  { Range(f) : f \in ChoiceFunction(Sets) }

-----------------------------------------------------------------------------

(***************************************************************************)
(* Chooses unique element from the input set matching the predicate        *)
(* (LAMDBA) P.                                                             *)
(*                                                                         *)
(* Contrary to CHOOSE, fails with                                          *)
(*      "CHOOSE x \\in S: P, but no element of S satisfied P:              *)
(* not just if P(_) holds for none of the elements in S, but also if       *)
(* P(_) holds for more than one element in S.                              *)
(*                                                                         *)
(* Example:                                                                *)
(*          ChooseUnique({2, 3, 4, 5}, LAMBDA x : x % 3 = 1) = 4           *)
(*                                                                         *)
(***************************************************************************)
ChooseUnique(S, P(_)) == CHOOSE x \in S :
                              P(x) /\ \A y \in S : P(y) => y = x

=============================================================================
