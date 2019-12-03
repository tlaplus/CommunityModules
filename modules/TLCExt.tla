------------------------------- MODULE TLCExt -------------------------------

LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

\* AssertEq(a, b) is logically equivalent to the expression 'a = b'. If a and b are not equal, 
\* however, AssertEq(a, b) will print out the values of 'a' and 'b'. If the two values are equal,
\* nothing will be printed.
AssertEq(a, b) == 
    IF a # b THEN
        /\ PrintT("Assertion failed")
        /\ PrintT(a)
        /\ PrintT(b)
        /\ a = b
    ELSE a = b

PickSuccessor(exp) ==
  (******************************************************************************)
  (* When set as an action constraint in the configuration file, interactively  *)
  (* pick successor states during state exploration, iff the expression exp     *)
  (* evaluates to FALSE.  To always pick successor states manually, use         *)
  (* PickSuccessor(FALSE). To pick successor states when the current prefix of  *)
  (* behaviors exceeds 22 states, use PickSuccessor(TLCGet("level") < 23).      *)
  (******************************************************************************)
  IF (exp)
  THEN TRUE
  ELSE CHOOSE bool \in BOOLEAN : TRUE 

=============================================================================
