---------------------------- MODULE CSVTests ----------------------------
EXTENDS CSV, TLC

ASSUME(
  CSVWrite(
    "%1$s#%2$s#%3$s", \* hash symbol is probably best separator for TLA+. 
    << 42, "abc", [a |-> "a", b |-> "b"] >>,
    "/tmp/out.csv"))

=============================================================================
                                                                    
