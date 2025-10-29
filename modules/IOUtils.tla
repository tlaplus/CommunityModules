------------------------------ MODULE IOUtils ------------------------------
(***************************************************************************)
(* This module provides operators for input/output operations and          *)
(* external process execution. All operators are overridden by Java        *)
(* implementations that perform the actual I/O operations.                 *)
(*                                                                         *)
(* The module enables TLA+ specifications to:                              *)
(*   - Execute external commands and capture their output                  *)
(*   - Serialize/deserialize TLA+ values to/from files                     *)
(*   - Access environment variables                                        *)
(*   - Interface with external systems during model checking               *)
(*                                                                         *)
(* Note: Some operators in this module evaluate to TRUE in TLA+ but        *)
(* perform side effects when executed by TLC with the Java overrides.      *)
(***************************************************************************)

LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

(***************************************************************************)
(* Serializes the given value to the file in Java's object serialization   *)
(* format.                                                                 *)
(*                                                                         *)
(* Parameters:                                                             *)
(*   - val: The TLA+ value to serialize                                    *)
(*   - absoluteFilename: Absolute path to the output file                  *)
(*   - compress: Boolean indicating whether to compress the output         *)
(***************************************************************************)
IOSerialize(val, absoluteFilename, compress) == TRUE

(***************************************************************************)
(* Deserializes a TLA+ value from a file in Java's object serialization    *)
(* format.                                                                 *)
(*                                                                         *)
(* Parameters:                                                             *)
(*   - absoluteFilename: Absolute path to the input file                   *)
(*   - compressed: Boolean indicating whether the file is compressed       *)
(*                                                                         *)
(* Returns the deserialized TLA+ value.                                    *)
(***************************************************************************)
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
(*     IN IOEnvExec(ENV, <<"ls", "-lah", "/tmp">>)                             *)
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

(***************************************************************************)
(* Converts a string representation of a number to a number.               *)
(*                                                                         *)
(* This is useful for processing environment variables or command output   *)
(* that contains numeric values as strings.                                *)
(*                                                                         *)
(* Examples:                                                               *)
(*   atoi("42") = 42                                                       *)
(*   atoi("-17") = -17                                                     *)
(*   atoi("0") = 0                                                         *)
(*                                                                         *)
(* Usage with environment variables:                                       *)
(*   Assuming environment variable PORT is set to "8080":                  *)
(*   atoi(IOEnv.PORT) = 8080                                               *)
(***************************************************************************)
atoi(str) ==
  CHOOSE i \in Int : ToString(i) = str

(***************************************************************************)
(* Pads a natural number with leading zeros to achieve a specified width.  *)
(*                                                                         *)
(* This function converts a natural number to a string and pads it with    *)
(* leading zeros if necessary to reach the specified width. If the         *)
(* number's string representation is already equal to or longer than the   *)
(* specified width, no padding is added.                                   *)
(*                                                                         *)
(* Parameters:                                                             *)
(*   - n: The natural number to be padded (must be >= 0)                   *)
(*   - width: The desired total width of the resulting string              *)
(*                                                                         *)
(* Examples:                                                               *)
(*   zeroPadN(42, 5) = "00042"                                             *)
(*   zeroPadN(123, 3) = "123"                                              *)
(*   zeroPadN(7, 1) = "7"                                                  *)
(*   zeroPadN(0, 4) = "0000"                                               *)
(*                                                                         *)
(* Note: Negative numbers are not supported and may produce unexpected     *)
(* results.                                                                *)
(*                                                                         *)
(* Returns a sequence of characters representing the zero-padded number.   *)
(***************************************************************************)
zeroPadN(n, width) ==
    LET s == ToString(n)
        padLen == width - Len(s)
        zeros == [i \in 1..padLen |-> "0"]
    IN FoldLeft(LAMBDA acc, z: acc \o z, "", zeros) \o s
============================================================================
