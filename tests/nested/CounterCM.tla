----- MODULE CounterCM -----
EXTENDS IOUtils, TLC, Naturals

ASSUME PrintT("IOUtilsTests!C!d!CounterCM")

VARIABLE x

\* SOME_TEST_ENV_VAR comes from the outermost build.xml.
ASSUME(LET ret == IOExec(<<"/bin/sh", "-c", "echo $SOME_TEST_ENV_VAR">>)
                                        IN /\ ret.stdout = "TLCFTW\n"
                                           /\ ret.exitValue = 0
                                           /\ ret.stderr = "")
ASSUME(IOEnv.SOME_TEST_ENV_VAR = "TLCFTW")

\* SOME_NESTED_VAR passed by IOUtilsTest.tla.
ASSUME(LET ret == IOExec(<<"/bin/sh", "-c", "echo $SOME_NESTED_VAR">>)
                                        IN /\ ret.stdout = "SOME_VAL\n"
                                           /\ ret.exitValue = 0
                                           /\ ret.stderr = "")
ASSUME(IOEnv.SOME_NESTED_VAR = "SOME_VAL")

\* B passed by IOUtilsTest.tla.
ASSUME(IOExec(<<"/bin/sh", "-c", "echo $B">>).stdout = "23\n")
ASSUME(IOEnv.B = "23")

ASSUME LET n  == CHOOSE n \in 0..100 : IOEnv.B = ToString(n)
       IN n = 23

INSTANCE Counter WITH UpperBound <- 3

============================
