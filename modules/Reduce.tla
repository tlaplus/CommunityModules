This module provides an operator to do folds without having to use RECURSIVE operators.
It assumes that we're working over an abelian operation. Caveat Emptor.

-------------------------------- MODULE Reduce --------------------------------


(***************************************************************************)
(* TLA+ forbids recursive higher-order operators, but it is fine with      *)
(* recursive functions.  ReduceSet generates a recursive function over the *)
(* subsets of a set, which can be used to recursively run a defined        *)
(* operator.  This can then be used to define other recursive operators.   *)
(***************************************************************************)

ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] == \* here's where the magic is
    IF s = {} THEN acc
    ELSE LET x == CHOOSE x \in s: TRUE
         IN op(x, f[s \ {x}])
  IN f[set]


Sum(set) == ReduceSet(LAMBDA x, y: x + y, set, 0)
Product(set) == ReduceSet(LAMBDA x, y: x * y, set, 1)

ReduceSeq(op(_, _), seq, acc) == 
  (***************************************************************************)
  (* We can't just apply ReduceSet to the Range(seq) because the same        *)
  (* element might appear twice in the sequence.                             *)
  (***************************************************************************)
  ReduceSet(LAMBDA i, a: op(seq[i], a), DOMAIN seq, acc)

=============================================================================
