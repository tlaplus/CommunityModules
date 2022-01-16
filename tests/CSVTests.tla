---------------------------- MODULE CSVTests ----------------------------
EXTENDS CSV, TLC, Sequences, IOUtils, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("CSVTests")

Template ==
    \* '#' symbol is probably best separator for TLA+.
    "%1$s#%2$s#%3$s"

Value ==
    << 42, "abc", [a |-> "a", b |-> "b"] >>

ToFile == 
    "build/tests/CSVWriteTest-" \o ToString(JavaTime) \o ".csv"

\* Write Value to ToFile then check success by reading with IOExec. 
ASSUME
  CSVWrite(Template, Value, ToFile) 
    => 
      /\ CSVRecords(ToFile) = 1
      \* Skip the third (record) element because it would come back as a string.
      /\ LET in == Head(CSVRead(<<"a", "b", "c">>, "#", ToFile))
         IN in.a = "42" /\ in.b = "\"abc\"" /\ in.c = "[a |-> \"a\", b |-> \"b\"]"

ASSUME
  CSVRecords("DoesNotExistNowhere.tla") = 0
  
=============================================================================
                                                                    
