------------------------------ MODULE IOUtils ------------------------------

LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

IOSerialize(val, absoluteFilename, compress) == TRUE

IODeserialize(absoluteFilename, compressed) == CHOOSE val : TRUE

----------------------------------------------------------------------------

IOExec(command, parameters) == 
  (*************************************************************************)
  (* Spawns the given printf-style command as a sub-process of TLC.  The   *)
  (* n-th flag in command is substituted for the n-th element of the       *)
  (* sequence parameters: IOExec("ls %s %s", <<"-lah", "/tmp">>)           *)
  (* see http://docs.oracle.com/javase/7/docs/api/java/util/Formatter.html *)
  (*************************************************************************)
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

============================================================================
