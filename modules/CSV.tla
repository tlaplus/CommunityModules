-------------------------------- MODULE CSV --------------------------------

LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

CSVWrite(template, val, file) == 
   (*
       CSVWrite("%1$s#%2$s#%3$s", 
           <<"abc", 42, {"x", "y"} >>, "/tmp/out.csv")
    *)
   TRUE

CSVWriteRecord(record, delim, headers, file) == 
   (*
       CSVWriteRecord([foo |-> 42] @@ [bar |-> "frob"], 
           CSVRecords("/tmp/out.csv") = 0, "#", "/tmp/out.csv")
    *)
   TRUE

CSVRead(columns, delimiter, file) == 
   (*
       CSVRead(<<"C1", "C2", "C3">>, "#", "/tmp/out.csv")
       
       << [ C1 |-> "\"abc\"", C2 |-> "42", C3 |-> "{"\"x\"", "\"y\""}" ] >>
    *)
   TRUE


CSVRecords(file) == 
   (* The number of records in the given file (including headers if any). *)
   CHOOSE n : n \in Nat

============================================================================
