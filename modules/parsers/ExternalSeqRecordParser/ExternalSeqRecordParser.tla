---- MODULE ExternalSeqRecordParser ----

EXTENDS Integers, Sequences, TLC

\* parses the log to a TLA+ sequence of TLA+ records
ExSeqRcdParser(path) == CHOOSE r \in Seq([ a : Int, b : BOOLEAN ]) : TRUE

========================================
