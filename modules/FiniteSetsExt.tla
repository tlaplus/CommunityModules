--------------------------- MODULE FiniteSetsExt ---------------------------
EXTENDS Naturals, FiniteSets, Functions


ReduceSet(op(_, _), set, acc) ==
  (***************************************************************************)
  (* TLA+ forbids recursive higher-order operators, but it is fine with      *)
  (* recursive functions.  ReduceSet generates a recursive function over the *)
  (* subsets of a set, which can be used to recursively run a defined        *)
  (* operator.  This can then be used to define other recursive operators.   *)
  (* The op is assumed to be an abelian/commutative operation.               *)
  (***************************************************************************)
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc
    ELSE LET x == CHOOSE x \in s: TRUE
         IN op(x, f[s \ {x}])
  IN f[set]


Sum(set) == ReduceSet(LAMBDA x, y: x + y, set, 0)

Product(set) == ReduceSet(LAMBDA x, y: x * y, set, 1)

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

=============================================================================
