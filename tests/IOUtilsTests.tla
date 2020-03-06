---------------------------- MODULE IOUtilsTests ----------------------------
EXTENDS IOUtils, TLC

\* Spaces and quotes should be passed directly to the program.
ASSUME(LET ret == IOExec(<<"echo", "'foo' ", " \"bar\"">>) IN /\ ret.exitValue = 0
                                                              /\ ret.stdout = "'foo'   \"bar\"\n"
                                                              /\ ret.stderr = "")
\* Exit values and standard error should be returned properly.
ASSUME(LET ret == IOExec(<<"cat",  "/does/not/exist">>) IN /\ ret.exitValue = 1
                                                           /\ ret.stdout = ""
                                                           /\ ret.stderr = "cat: /does/not/exist: No such file or directory\n")

=============================================================================
