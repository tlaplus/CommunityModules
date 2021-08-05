------------------------- MODULE CombinatoricsTests -------------------------
EXTENDS Combinatorics

ASSUME LET T == INSTANCE TLC IN T!PrintT("CombinatoricsTests")

ASSUME LET RECURSIVE factorialPure(_)
           factorialPure(n) == IF n = 0 THEN 1 ELSE n * factorialPure(n-1)
       IN \A n \in (0..12) : factorial[n] = factorialPure(n)

ASSUME LET choosePure(n, k) ==
                factorial[n] \div (factorial[k] * factorial[n - k])
       IN \A n,k \in (0..12) : (n >= k) => choosePure(n, k) = choose(n, k)

ASSUME \A n \in 0..63:
            /\ choose(n, 0) = 1
            /\ choose(n, n) = 1 
            /\ choose(n, 1) = n

=============================================================================
