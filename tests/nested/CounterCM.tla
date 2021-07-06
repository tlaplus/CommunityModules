----- MODULE CounterCM -----
EXTENDS IOUtils, TLC

VARIABLE x

\* SOME_TEST_ENV_VAR comes from the outermost build.xml.
ASSUME(LET ret == IOExec(<<"/bin/bash", "-c", "echo $SOME_TEST_ENV_VAR">>)
                                        IN /\ ret.stdout = "TLCFTW\n"
                                           /\ ret.exitValue = 0
                                           /\ ret.stderr = "")

INSTANCE Counter WITH UpperBound <- 3

============================
