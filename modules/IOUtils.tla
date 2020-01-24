------------------------------ MODULE IOUtils ------------------------------

LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

IOSerialize(val, absoluteFilename, compress) == TRUE

IODeserialize(absoluteFilename, compressed) == CHOOSE val : TRUE

============================================================================

\* Writes a TLA+ expression to the given file.
\* TODO: Decide if it should write a module preamble.
\* Write is easier to implement than Read because it goes from (valid) TLA+
\* and writes a file whereas Read has to parse it.
IOWrite(exp, absoluteFilename) == TRUE

\* Reads a TLA+ expression from a file.
\* TODO: Decide if it reads just a string from a file or expects (valid) TLA+.
\*         For trace validation it would be preferable to read strings.
\*       Constant-level expression (what's a use-case to read fileS during state space exploration?
IORead(absoluteFilename) == TRUE

TLAParse(IORead("C:\\foo\bar"))

(* condition generally of level up to action (but not temporal), e.g. Inv'.  *)

\* Run the given OS command if condition evaluates to true.
\* This is novel and cannot be done otherwise.
\* TODO: What to pass to os command? osCommand a string that a user munges directly
\*       in/with TLA+.
\*       Can IOWrite/IORead be spec'ed with IOExec?
IOExec(condition, osCommand) == TRUE

=============================================================================
