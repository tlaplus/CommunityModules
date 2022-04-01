------------------------------ MODULE IOUtils ------------------------------

LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

\* @supportedBy("TLC")
IOSerialize(val, absoluteFilename, compress) == TRUE

\* @supportedBy("TLC")
IODeserialize(absoluteFilename, compressed) == CHOOSE val : TRUE

\* @supportedBy("TLC")
Serialize(value, dest, options) ==
  (*******************************************************************************)
  (* value: TLA+ value to be serialized.                                         *)
  (* dest: Destination to serialize to such as a file or URL.                    *)
  (* options: Record of serializer-specific options with format mandatory to     *)
  (* identify a serializer.  Read a seriazlier's documentation for serializer-   *)
  (* specific options.                                                           *)
  (*******************************************************************************)
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

\* @supportedBy("TLC")
Deserialize(src, options) ==
  (*******************************************************************************)
  (* src: Destination to serialize to such as a file or URL.                     *)
  (* options: Record of serializer-specific options with format mandatory to     *)
  (* identify a serializer.  Read a seriazlier's documentation for serializer-   *)
  (* specific options.                                                           *)
  (*******************************************************************************)
  CHOOSE val : TRUE

----------------------------------------------------------------------------

\* @supportedBy("TLC")
IOExec(command) ==
  (*******************************************************************************)
  (* Spawns the given command as a sub-process of TLC.  The sequence of sequence *)
  (* of strings `command' signifies the external program file to be invoked and  *)
  (* its arguments:                                                              *)
  (*     IOExec(<<"ls", "-lah", "/tmp">>)                                        *)
  (*     IOExec(<<"bash", "-c", "echo \"Col1#Col2\" > /tmp/out.csv">>            *)
  (* see https://docs.oracle.com/javase/7/docs/api/java/lang/ProcessBuilder.html *)
  (*******************************************************************************)
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

\* @supportedBy("TLC")
IOEnvExec(env, command) ==
  (*******************************************************************************)
  (* See IOExec                                                                  *)
  (*     LET ENV = {<<"Var1", "SomeVal">>, <<"Var2", 42>>}                       *)
  (*     IN IOEnvExec(ENV, <<"ls", "-lah", "/tmp">>)                            *)
  (*******************************************************************************)
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

\* @supportedBy("TLC")
IOExecTemplate(commandTemplate, parameters) ==
  (*************************************************************************)
  (* Spawns the given printf-style command as a sub-process of TLC.  The   *)
  (* n-th flag in `commandTemplate' is substituted with the n-th element   *)
  (* of the sequence `parameters':                                         *)
  (*     IOExecTemplate(<<"ls", "%s" "%s">>, <<"-lah", "/tmp">>)           *)
  (*     IOExecTemplate(<<"ls %1$s %2$s">>, <<"-lah", "/tmp">>)            *)
  (* see http://docs.oracle.com/javase/7/docs/api/java/util/Formatter.html *)
  (*************************************************************************)
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

\* @supportedBy("TLC")
IOEnvExecTemplate(env, commandTemplate, parameters) ==
  (*******************************************************************************)
  (* See IOExecTemplate                                                          *)
  (*     LET ENV = {<<"Var1", "SomeVal">>, <<"Var2", 42>>}                       *)
  (*     IN IOEnvExecTemplate(ENV, <<"ls", "-lah", "/tmp">>)                     *)
  (*******************************************************************************)
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE

\* @supportedBy("TLC")
IOEnv ==
  (*************************************************************************)
  (* The process' environment variables.                                   *)
  (*************************************************************************)
  CHOOSE r \in [STRING -> STRING] : TRUE

\* @supportedBy("TLC")
atoi(str) ==
  (*************************************************************************)
  (* Assuming the environment variable  SomeEnvVar  is set to  42,         *)
  (*  atoi(IOEnv.SomeEnvVar)  equals  42  .                                *)
  (*************************************************************************)
  CHOOSE i \in Int : ToString(i) = str

============================================================================
