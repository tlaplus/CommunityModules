------------------------- MODULE Combinatorics -------------------------
EXTENDS Naturals

\* @supportedBy("TLC")
factorial[n \in Nat] == 
    IF n = 0 THEN 1 ELSE n * factorial[n-1]

\* @supportedBy("TLC")
choose(n, k) ==
    factorial[n] \div (factorial[k] * factorial[n - k])

=========================================================================
