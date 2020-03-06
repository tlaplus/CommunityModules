------------------------------ MODULE IOUtils ------------------------------

LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

IOSerialize(val, absoluteFilename, compress) == TRUE

IODeserialize(absoluteFilename, compressed) == CHOOSE val : TRUE

----------------------------------------------------------------------------

IOExec(command) ==
  (*******************************************************************************)
  (* Spawns the given command as a sub-process of TLC.  The sequence of sequence *)
  (* of strings `command' signifies the external program file to be invoked and  *)
  (* its arguments: IOExec(<<"ls", "-lah", "/tmp">>)                             *)
  (* see https://docs.oracle.com/javase/7/docs/api/java/lang/ProcessBuilder.html *)
  (*******************************************************************************)
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

============================================================================
