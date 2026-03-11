---------------------------- MODULE IOUtilsTests ----------------------------
EXTENDS IOUtils, TLC, TLCExt, Integers

ASSUME PrintT("IOUtilsTests!A")

\* SOME_TEST_ENV_VAR is set in Ant's build.xml file.
\* The IOEnv operator does *not* append a dangling newline to the value (contrary to
\* reading env vars via /bin/sh -c echo).  Environment variable names made out of
\* non-legal chars for TLA+ records can fall back to ordinary function application.

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

ASSUME PrintT("IOUtilsTests!B")

\* Simple round-trip test with a variety of different small structures

file == "build/tests/bin-serialize-test.vos"
payloadBIN == <<
	"foo",
	{"bar"},
	42,
	1..3,
	[x |-> 1, y |-> 2]
>>

ASSUME /\ IOSerialize(payloadBIN, file, FALSE)
       /\ LET value == IODeserialize(file, FALSE)
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
