----- MODULE CounterCM -----
EXTENDS IOUtils, TLC

VARIABLE x

\* SOME_TEST_ENV_VAR comes from the outermost build.xml.
ASSUME(LET ret == IOExec(<<"/bin/sh", "-c", "echo $SOME_TEST_ENV_VAR">>)
                                        IN /\ ret.stdout = "TLCFTW\n"
                                           /\ ret.exitValue = 0
                                           /\ ret.stderr = "")

\* SOME_NESTED_VAR passed by IOUtilsTest.tla.
ASSUME(LET ret == IOExec(<<"/bin/sh", "-c", "echo $SOME_NESTED_VAR">>)
                                        IN /\ ret.stdout = "SOME_VAL\n"
                                           /\ ret.exitValue = 0
                                           /\ ret.stderr = "")

\* B passed by IOUtilsTest.tla.
ASSUME(IOExec(<<"/bin/sh", "-c", "echo $B">>).stdout = "23\n")

INSTANCE Counter WITH UpperBound <- 3

============================
