--------------------------- MODULE FiniteSetsExt ---------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Functions
LOCAL INSTANCE Folds

FoldSet(op(_,_), base, set) ==
   (*************************************************************************)
   (* Fold op over the elements of set using base as starting value.        *)
   (*                                                                       *)
   (* Intuitive semantics:                                                  *)
   (* Initialize a temporary variable `accum` with the value of `base`.     *)
   (* Iterate over the elements in set in a deterministic but unknown       *)
   (* order pdate the value of `accum` to the value of `op(accum, x`),      *)
   (* where `x` s the current value of the iterator.                        *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*         FoldSet(LAMBA x,y : x + y, 0 .. 10, 0) = 55                   *)
   (*************************************************************************)
   MapThenFoldSet(op, base, LAMBDA x : x, set)

Sum(set) ==
   (*************************************************************************)
   (* Calculuate the sum of the elements in set.                            *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*         Sum(0 .. 10) = 55                                             *)
   (*************************************************************************)
   FoldSet(LAMBDA x, y: x + y, set, 0)

Product(set) ==
   (*************************************************************************)
   (* Calculuate the product of the elements in set.                        *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*         Product(0 .. 10) = 55                                         *)
   (*************************************************************************)
   FoldSet(LAMBDA x, y: x * y, set, 1)

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
