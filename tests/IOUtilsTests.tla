---------------------------- MODULE IOUtilsTests ----------------------------
EXTENDS IOUtils, TLC, TLCExt, Integers

ASSUME PrintT("IOUtilsTests!A")

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

ASSUME PrintT("IOUtilsTests!B")

(***********************************************************************)
(* Check that environment variables work with IOUtils!IOExec operator: *)
(***********************************************************************)

\* SOME_TEST_ENV_VAR is set in Ant's build.xml file.

ASSUME(LET ret == IOExec(<<"/bin/sh", "-c", "echo $SOME_TEST_ENV_VAR">>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "TLCFTW\n"
                                                                    /\ ret.stderr = "")

ASSUME(LET ret == IOEnvExec([SOME_VAR_42 |-> "42"], <<"/bin/sh", "-c", "echo $SOME_VAR_42">>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "42\n"
                                                                    /\ ret.stderr = "")

ASSUME(LET ret == IOEnvExecTemplate([SOME_VAR_42 |-> "42"], <<"/bin/sh", "-c", "echo $SOME_VAR_42">>, <<>>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "42\n"
                                                                    /\ ret.stderr = "")

ASSUME(LET ret == IOEnvExecTemplate([SOME_VAR_42 |-> "42"], <<"/bin/sh", "-c", "echo $SOME_VAR_42">>, <<>>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "42\n"
                                                                    /\ ret.stderr = "")

ASSUME(LET ret == IOEnvExecTemplate([A |-> 1, B |-> 2], <<"/bin/sh", "-c", "echo $A $B">>, <<>>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "1 2\n"
                                                                    /\ ret.stderr = "")

ASSUME(LET ret == IOEnvExec(IOEnv, <<"/bin/sh", "-c", "echo $SOME_TEST_ENV_VAR">>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "TLCFTW\n"
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

ASSUME(atoi("1") = 1)
ASSUME(atoi("0") = 0)
ASSUME(atoi("-0") = 0)
ASSUME(atoi("-1") = -1)

ASSUME AssertError(
           "The argument of atoi should be a string, but instead it is:\n\"\"", 
           atoi(""))
ASSUME AssertError(
           "The argument of atoi should be a string, but instead it is:\n\"foo\"", 
           atoi("foo"))

\* Test zeroPadN function with various inputs
ASSUME(AssertEq(zeroPadN(42, 5), "00042"))
ASSUME(AssertEq(zeroPadN(123, 3), "123"))
ASSUME(AssertEq(zeroPadN(7, 1), "7"))
ASSUME(AssertEq(zeroPadN(0, 4), "0000"))
ASSUME(AssertEq(zeroPadN(999, 2), "999"))
ASSUME(AssertEq(zeroPadN(1000, 6), "001000"))
ASSUME(AssertEq(zeroPadN(0, 1), "0"))

---------------------------------------------------------------------------------------------------------------------------

ASSUME PrintT("IOUtilsTests!C")

(***********************************************************************)
(* Check that TLC can be launched through the IOUtils!IOExec operator: *)
(***********************************************************************)

\* Exit if tlc/tla2tools.jar doesn't exist.  Since the tests are run with this tla2tools.jar, this assumption should hold.
ASSUME(LET ret == IOExec(<<"ls", "tlc/tla2tools.jar">>) 
                                                                 IN /\ ret.exitValue = 0
                                                                    /\ ret.stdout = "tlc/tla2tools.jar\n"
                                                                    /\ ret.stderr = "")

ASSUME PrintT("IOUtilsTests!C!b")

\* Run TLC without any parameters.  TLC prints its version number, git commit, ... to stdout and sets RETVAL ($?) to 1.
ASSUME(LET ret == IOExec(<<"java", "-jar", "tlc/tla2tools.jar">>)
                                                                 IN /\ PrintT(ret)
                                                                    /\ ret.exitValue = 1
                                                                    /\ ret.stderr = "")

ASSUME PrintT("IOUtilsTests!C!c")

\* Run TLC with some basic spec that passes.
ASSUME(LET ret == IOExec(<<"java", "-jar", "tlc/tla2tools.jar", "tests/nested/Counter">>)
                                                                 IN /\ PrintT(ret)
                                                                    /\ ret.exitValue = 0
                                                                    /\ ret.stderr = "")

ASSUME PrintT("IOUtilsTests!C!d")

\* Run TLC with some spec depending on CommunityModules and CM on the classpath.
\* Pass an environment variable to the nested spec.
ASSUME(LET ret == IOEnvExec([SOME_NESTED_VAR |-> "SOME_VAL", B |-> "23"],
                            <<"java", "-cp", "modules:build/deps:build/modules:tlc/tla2tools.jar", "tlc2.TLC",
                                          "-config", "Counter.cfg", "tests/nested/CounterCM">>)
                                                                 IN /\ PrintT(ret)
                                                                    /\ ret.exitValue = 0
                                                                    /\ ret.stderr = "")

---------------------------------------------------------------------------------------------------------------------------

ASSUME PrintT("IOUtilsTests!D")

ASSUME PrintT("IOUtilsTests!D!A")

file == "/tmp/txt-serialize-test.txt"
payloadTXT == "Some text with \" escapes \" \\"

TXTSerializeResult == Serialize(payloadTXT, file, [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>])
ASSUME(LET ret == TXTSerializeResult IN /\ ret.exitValue = 0
                                        /\ ret.stderr = "")

TXTDeserializeResult == Deserialize(file, [format |-> "TXT", charset |-> "UTF-8"])
ASSUME(LET ret == TXTDeserializeResult IN /\ ret.exitValue = 0
                                          /\ ret.stdout = payloadTXT
                                          /\ ret.stderr = "")
                                          
---------------------------------------------------------------------------------------------------------------------------                                      

\* Simple round-trip test with a variety of different small structures

file2 == "/tmp/bin-serialize-test.vos"
payloadBIN == <<
	"foo",
	{"bar"},
	42,
	1..3,
	[x |-> 1, y |-> 2]
>>

ASSUME /\ IOSerialize(payloadBIN, file2, FALSE)
       /\ LET value == IODeserialize(file2, FALSE)
          IN  value = payloadBIN

\* Test: can we read a string TLC has never encountered before?
\* !Danger: writing the string literal at any point in the TLA+ breaks the test!

\* The bug this tests for is that TLC can only read string values that are already interned in its
\* in-memory string table. If the string is so much as in the spec at all, TLC can load it.
\* If the string has was never interned however, then TLC would crash when accessing the value
\* (e.g., printing it), because the string table gives `null` on lookup.
\* The weird long name is chosen to avoid any other tests mentioning this string.
ASSUME LET strValue == IODeserialize("tests/Hippopotomonstrosesquippedaliophobia.vos", FALSE)
       IN /\ PrintT(strValue)
          \* Intended value (in a comment, so not "seen" by TLC)
          \* /\ strValue = "Hippopotomonstrosesquippedaliophobia"

=============================================================================
