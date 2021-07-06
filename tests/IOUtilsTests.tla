---------------------------- MODULE IOUtilsTests ----------------------------
EXTENDS IOUtils, TLC, Naturals

\* Spaces and quotes should be passed directly to the program.
ASSUME(LET ret == IOExec(<<"echo", "'foo' ", " \"bar\"">>) IN /\ ret.exitValue = 0
                                                              /\ ret.stdout = "'foo'   \"bar\"\n"
                                                              /\ ret.stderr = "")
\* Exit values and standard error should be returned properly.
ASSUME(LET ret == IOExec(<<"cat",  "/does/not/exist">>) IN /\ ret.exitValue = 1
                                                           /\ ret.stdout = ""
                                                           /\ ret.stderr = "cat: /does/not/exist: No such file or directory\n")

\* Spaces and quotes should be passed directly to the program.
ASSUME(LET ret == IOExecTemplate(<<"bash", "-c", "echo %1$s %2$s">>, <<"foo", "bar">>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "foo bar\n"
                                                                    /\ ret.stderr = "")

\* Spaces and quotes should be passed directly to the program.
ASSUME(LET ret == IOExecTemplate(<<"echo", "'%1$s'", "\"%2$s\"">>, <<" foo", "bar ">>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "' foo' \"bar \"\n"
                                                                    /\ ret.stderr = "")

\* Exit values and standard error should be returned properly.
ASSUME(LET ret == IOExecTemplate(<<"cat", "/does/not/exist">>, <<>>) 
                                                              IN /\ ret.exitValue = 1
                                                                 /\ ret.stdout = ""
                                                                 /\ ret.stderr = "cat: /does/not/exist: No such file or directory\n")

---------------------------------------------------------------------------------------------------------------------------

(***********************************************************************)
(* Check that environment variables work with IOUtils!IOExec operator: *)
(***********************************************************************)

\* SOME_TEST_ENV_VAR is set in Ant's build.xml file.

ASSUME(LET ret == IOExec(<<"/bin/sh", "-c", "echo $SOME_TEST_ENV_VAR">>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "TLCFTW\n"
                                                                    /\ ret.stderr = "")

ASSUME(LET ret == IOEnvExec({<<"SOME_VAR_42","42">>}, <<"/bin/sh", "-c", "echo $SOME_VAR_42">>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "42\n"
                                                                    /\ ret.stderr = "")

ASSUME(LET ret == IOEnvExecTemplate({<<"SOME_VAR_42","42">>}, <<"/bin/sh", "-c", "echo $SOME_VAR_42">>, <<>>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "42\n"
                                                                    /\ ret.stderr = "")

ASSUME(LET ret == IOEnvExecTemplate({<<"SOME_VAR_42","42">>}, <<"/bin/sh", "-c", "echo $SOME_VAR_42">>, <<>>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "42\n"
                                                                    /\ ret.stderr = "")


\* Contrary to the /bin/sh -c echo $SOME_VAR technique above, the IOEnv operator does *not* append a dangling
\* newline to the value.  Environment variable names made out of non-legal chars for TLA+ records can fall
\* back to ordinary function application.

ASSUME(IOEnv.SOME_TEST_ENV_VAR = "TLCFTW")
ASSUME(IOEnv["SOME_TEST_ENV_VAR"] = "TLCFTW")
ASSUME(IOEnv["SOME-TEST-ENV-VAR"] = "TLCFTW")

\* Test/show how to convert (the set) "23" to (the set) 23.
ASSUME LET n  == CHOOSE n \in 0..2^16 : \* TLC won't choose from *unbounded*  Nat  , thus restricting to 0..2^16 (which should be sufficient for most use cases).
			                  IOEnv.SOME_TEST_ENV_VAR_N23 = ToString(n)
       IN n = 23

ASSUME(DOMAIN IOEnv \subseteq STRING)
ASSUME(\A var \in DOMAIN IOEnv: IOEnv[var] \in STRING)

---------------------------------------------------------------------------------------------------------------------------

(***********************************************************************)
(* Check that TLC can be launched through the IOUtils!IOExec operator: *)
(***********************************************************************)

\* Exit if tlc/tla2tools.jar doesn't exist.  Since the tests are run with this tla2tools.jar, this assumption should hold.
ASSUME(LET ret == IOExec(<<"ls", "tlc/tla2tools.jar">>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "tlc/tla2tools.jar\n"
                                                                    /\ ret.stderr = "")


\* Run TLC without any parameters.  TLC prints its version number, git commit, ... to stdout and sets RETVAL ($?) to 1.
ASSUME(LET ret == IOExec(<<"java", "-jar", "tlc/tla2tools.jar">>)
                                                                 IN /\ ret.exitValue = 1
                                                                    /\ ret.stderr = "")


\* Run TLC with some basic spec that passes.
ASSUME(LET ret == IOExec(<<"java", "-jar", "tlc/tla2tools.jar", "tests/nested/Counter">>)
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stderr = "")

\* Run TLC with some spec depending on CommunityModules and CM on the classpath.
\* Pass an environment variable to the nested spec.
ASSUME(LET ret == IOEnvExec({<<"SOME_NESTED_VAR", "SOME_VAL">>, <<"B", "23">>},
                            <<"java", "-cp", "modules:build/modules:tlc/tla2tools.jar", "tlc2.TLC",
                                          "-config", "Counter.cfg", "tests/nested/CounterCM">>)
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stderr = "")
=============================================================================
