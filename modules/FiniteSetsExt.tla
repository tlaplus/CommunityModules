--------------------------- MODULE FiniteSetsExt ---------------------------
EXTENDS Naturals, FiniteSets


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
   (* This operator is overridden by FiniteSetsExt#quantify whose           *)
   (* implementation does *not* enumerate the intermediate set! This is     *)
   (* the only advantage that Quantify(...) has over Cardinality(...).      *)
   (*                                                                       *)
   (* Example:                                                              *)
   (*          Quantify(1..9, LAMBDA n : n % 2 = 0) = 4                     *)
   (*************************************************************************)
   Cardinality({s \in S : P(s)})

=============================================================================
