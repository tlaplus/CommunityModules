--------------------------- MODULE FiniteSetsExt ---------------------------
EXTENDS Naturals


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

=============================================================================
