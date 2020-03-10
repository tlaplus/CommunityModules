---- MODULE TLCExtTrace ----

EXTENDS Integers, TLC, TLCExt

VARIABLE x

Spec == x = 1 /\ [][x < 10 /\ x' = x + 1]_x

Inv == \/ x = 1
       \/ PrintT(<<Trace, x>>)
       
==================================

