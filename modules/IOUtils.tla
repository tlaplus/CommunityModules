------------------------------ MODULE IOUtils ------------------------------

LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

IOSerialize(val, absoluteFilename, compress) == TRUE

IODeserialize(absoluteFilename, compressed) == CHOOSE val : TRUE

(*******************************************************************************)
(* value: TLA+ value to be serialized.                                         *)
(* dest: Destination to serialize to such as a file or URL.                    *)
(* options: Record of serializer-specific options with format mandatory to     *)
(* identify a serializer.  Read a seriazlier's documentation for serializer-   *)
(* specific options.                                                           *)
(*******************************************************************************)
Serialize(value, dest, options) ==
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

(*******************************************************************************)
(* src: Destination to serialize to such as a file or URL.                     *)
(* options: Record of serializer-specific options with format mandatory to     *)
(* identify a serializer.  Read a seriazlier's documentation for serializer-   *)
(* specific options.                                                           *)
(*******************************************************************************)
Deserialize(src, options) ==
  CHOOSE val : TRUE

----------------------------------------------------------------------------

(*******************************************************************************)
(* Spawns the given command as a sub-process of TLC.  The sequence of sequence *)
(* of strings `command' signifies the external program file to be invoked and  *)
(* its arguments:                                                              *)
(*     IOExec(<<"ls", "-lah", "/tmp">>)                                        *)
(*     IOExec(<<"bash", "-c", "echo \"Col1#Col2\" > /tmp/out.csv">>            *)
(* see https://docs.oracle.com/javase/7/docs/api/java/lang/ProcessBuilder.html *)
(*******************************************************************************)
IOExec(command) ==
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

(*******************************************************************************)
(* See IOExec                                                                  *)
(*     LET ENV = {<<"Var1", "SomeVal">>, <<"Var2", 42>>}                       *)
(*     IN IOEnvExec(ENV, <<"ls", "-lah", "/tmp">>)                            *)
(*******************************************************************************)
IOEnvExec(env, command) ==
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

(*************************************************************************)
(* Spawns the given printf-style command as a sub-process of TLC.  The   *)
(* n-th flag in `commandTemplate' is substituted with the n-th element   *)
(* of the sequence `parameters':                                         *)
(*     IOExecTemplate(<<"ls", "%s" "%s">>, <<"-lah", "/tmp">>)           *)
(*     IOExecTemplate(<<"ls %1$s %2$s">>, <<"-lah", "/tmp">>)            *)
(* see http://docs.oracle.com/javase/7/docs/api/java/util/Formatter.html *)
(*************************************************************************)
IOExecTemplate(commandTemplate, parameters) ==
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

(*******************************************************************************)
(* See IOExecTemplate                                                          *)
(*     LET ENV = {<<"Var1", "SomeVal">>, <<"Var2", 42>>}                       *)
(*     IN IOEnvExecTemplate(ENV, <<"ls", "-lah", "/tmp">>)                     *)
(*******************************************************************************)
IOEnvExecTemplate(env, commandTemplate, parameters) ==
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

(*************************************************************************)
(* The process' environment variables.                                   *)
(*************************************************************************)
IOEnv ==
  CHOOSE r \in [STRING -> STRING] : TRUE

(*************************************************************************)
(* Assuming the environment variable  SomeEnvVar  is set to  42,         *)
(*  atoi(IOEnv.SomeEnvVar)  equals  42  .                                *)
(*************************************************************************)
atoi(str) ==
  CHOOSE i \in Int : ToString(i) = str

============================================================================
