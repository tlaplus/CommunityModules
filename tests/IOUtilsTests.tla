---------------------------- MODULE IOUtilsTests ----------------------------
EXTENDS IOUtils, TLC

ASSUME(LET ret == IOExec("echo %s %s", <<"foo", "bar">>) IN /\ ret.exitValue = 0 
                                                            /\ ret.stdout = "foo bar\n"
                                                            /\ ret.stderr = "")
ASSUME(LET ret == IOExec("cat /does/not/exist", <<>>) IN /\ ret.exitValue = 1 
                                                         /\ ret.stdout = ""
                                                         /\ ret.stderr = "cat: /does/not/exist: No such file or directory\n")
ASSUME(LET ret == IOExec("echo \"' %s", <<"\"'">>) IN /\ ret.exitValue = 0
                                                      /\ ret.stdout = "\"' \"'\n"
                                                      /\ ret.stderr = "")
ASSUME(LET ret == IOExec("grep %s /dev/null", <<"foo bar">>) IN /\ ret.exitValue = 1
                                                                /\ ret.stdout = ""
                                                                /\ ret.stderr = "")

=============================================================================
