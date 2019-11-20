------------------------------- MODULE Bitwise -------------------------------
LOCAL INSTANCE Integers

\* https://en.wikipedia.org/wiki/Bitwise_operation#Mathematical_equivalents
RECURSIVE And(_,_,_,_)
LOCAL And(x,y,n,m) == 
        LET exp == 2^n
        IN IF m = 0 
           THEN 0
           ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2) 
                    + And(x,y,n+1,m \div 2)

x & y == 
    (***************************************************************************)
    (* Bitwise AND of (non-negative) x and y (defined for Nat \cup {0}).       *)
    (***************************************************************************)
    And(x, y, 0, x) \* Infix variant of And(x,y)


RECURSIVE shiftR(_,_)
shiftR(n,pos) == 
    (***************************************************************************)
    (* Logical bit-shifting the (non-negative) n by pos positions to the right *)
    (* shifting zeros in from the left/MSB (defined for Nat \cup {0}).         *)
    (***************************************************************************)
    IF pos = 0 
    THEN n
    ELSE LET odd(z) == z % 2 = 1
             m == IF odd(n) THEN (n-1) \div 2 ELSE n \div 2
         IN shiftR(m, pos - 1)

=============================================================================
\* Modification History
\* Last modified Thu April 25 10:56:12 CEST 2018 by markus
\* Created Mon May 16 15:09:18 CEST 2016 by markus
