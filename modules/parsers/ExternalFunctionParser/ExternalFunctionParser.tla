---- MODULE ExternalFunctionParser ----

EXTENDS Integers, Sequences, TLC

\* parses the log to a TLA+ function
ExFunParser(path) == CHOOSE s \in [ Int -> Int ] : TRUE

=======================================
