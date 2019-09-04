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

=============================================================================
