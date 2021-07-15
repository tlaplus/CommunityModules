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

CSVRecords(file) == 
   (* The number of records in the given file (including headers if any). *)
   CHOOSE n : n \in Nat

============================================================================
