--------------------------- MODULE FiniteSetsExt ---------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Functions



(***************************************************************************)
(* Starting from base, apply op to f(x), for all x \in S, in an arbitrary  *)
(* order. It is assumed that op is associative and commutative.            *)
(***************************************************************************)
FoldMap(op(_,_), base, f(_), S) ==
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == CHOOSE x \in s : TRUE
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]

(*
   Intuitive semantics:

   Initialize a temporary variable `accum` with the value of `base`.  Iterate
   over the elements in set in a deterministic but unknown order, update the
   value of `accum` to the value of `op(accum, x`), where `x` is the current
   value of the iterator. The result of `FoldSet` is the computed value of
   `accum`.
 *)  
FoldSet(op(_,_), base, set) ==
  (*
    This is an implementation in terms of previously defined operators.
    A tool is free to define its own, more efficient, implementation.
   *) 
(*  ReduceSet(op, set, base) *)
  (* sm: alternative, equivalent definition *)
  FoldMap(op, base, LAMBDA x : x, set)

(***************************************************************************)
(* Fold over a function (or sequence).                                     *)
(***************************************************************************)
FoldFunction(op(_,_), base, fun) == 
  FoldMap(op, base, LAMBDA i : fun[i], DOMAIN fun)



(***************************************************************************)
(* Fold over a subset of the domain of a function -- corresponds to Reduce *)
(***************************************************************************)
FoldFunctionOnSet(op(_,_), base, fun, set) ==
  LET Squeeze(f, S) == [ s \in S |-> f[s]  ]
  IN
  FoldFunction(op, base, Squeeze(fun, set))


ReduceSet(op(_, _), set, acc) == FoldSet(op, set, acc)

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
