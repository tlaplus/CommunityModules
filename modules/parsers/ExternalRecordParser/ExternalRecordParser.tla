---- MODULE ExternalRecordParser ----

EXTENDS Integers, TLC

\* parses the log to a TLA+ record
ExRcdParser(path) == CHOOSE r \in [ a : Int, b : BOOLEAN ] : TRUE

=====================================
