----------------------------- MODULE CBORTests -----------------------------
EXTENDS CBOR, Integers, Sequences, FiniteSets, TLC, TLCExt

(***************************************************************************)
(* TLC sorts strings and record fields by the order in which it first saw  *)
(* them, not by their text.  These strings and field names appear here in  *)
(* the reverse of their CBOR order, before any other use, so TLC's own     *)
(* order disagrees with the CBOR order.  An encoder that relies on TLC's   *)
(* order then fails the golden tests "set-strings" and "record".           *)
(***************************************************************************)
LOCAL CBORInternFirst ==
    <<"cbor-zz", "cbor-aa", "cbor-a", [cborzz |-> 0, cboraa |-> 0, cbora |-> 0]>>

ASSUME LET T == INSTANCE TLC IN T!PrintT("CBORTests")

ASSUME AssertEq(ToString({"cbor-a", "cbor-zz"}), "{\"cbor-zz\", \"cbor-a\"}")
ASSUME AssertEq(ToString(DOMAIN [cbora |-> 0, cborzz |-> 0]), "{\"cborzz\", \"cbora\"}")

(***************************************************************************)
(* A golden test is an ASSUME that calls Golden or SameBytes with a name   *)
(* and the bytes that ToCBOR must return.  The JUnit test                  *)
(* tests/java/tlc2/overrides/CBORGoldenTest.java, an encoder that shares   *)
(* no code with CBOR.java, checks those bytes against its own encoding of  *)
(* the value it has under that name.                                       *)
(*                                                                         *)
(* All definitions are LOCAL because AllTests extends every test module.   *)
(***************************************************************************)

LOCAL INSTANCE IOUtils
LOCAL INSTANCE Json

\* The model value that tests/AllTests.cfg defines, without redeclaring the
\* constant that JsonTests declares.
LOCAL MV == TLCModelValue("ModelValue")

\* U+00E9, which enters as bytes so that this file stays ASCII.
LOCAL EAcute == FromCBOR(<<\h62, \hc3, \ha9>>)

LOCAL Golden(name, value, bytes) ==
    /\ AssertEq(ToCBOR(value), bytes)
    /\ AssertEq(FromCBOR(bytes), value)

\* TLC-equal values held in different Java classes encode as the same bytes.
LOCAL SameBytes(name, reps, bytes) == \A i \in DOMAIN reps : AssertEq(ToCBOR(reps[i]), bytes)

\* The bytes of a file as a string, one character per byte. A missing file fails instead of reading as "".
LOCAL FileText(file) ==
    LET r == Deserialize(file, [format |-> "TXT", charset |-> "ISO-8859-1"])
    IN IF r.exitValue = 0 THEN r.stdout ELSE Assert(FALSE, r.stderr)

-----------------------------------------------------------------------------

ASSUME Golden("int", <<0, 23, 24, 255, 256, 65535, 65536, 2147483647,
                       -1, -24, -25, -256, -257, -2147483647 - 1>>,
              <<\h8e, \h00, \h17, \h18, \h18, \h18, \hff, \h19, \h01, \h00, \h19, \hff, \hff, \h1a, \h00, \h01,
                \h00, \h00, \h1a, \h7f, \hff, \hff, \hff, \h20, \h37, \h38, \h18, \h38, \hff, \h39, \h01, \h00,
                \h3a, \h7f, \hff, \hff, \hff>>)
ASSUME Golden("bool", <<TRUE, FALSE>>, <<\h82, \hf5, \hf4>>)
ASSUME Golden("modelvalue", MV, <<\hd8, \h27, \h6a, \h4d, \h6f, \h64, \h65, \h6c, \h56, \h61, \h6c, \h75, \h65>>)
\* Bytewise order is 10, 100, -1. Length-first order is 10, -1, 100. TLC's order is -1, 10, 100.
ASSUME Golden("set", {100, -1, 10}, <<\hd9, \h01, \h02, \h83, \h0a, \h18, \h64, \h20>>)
ASSUME Golden("set-strings", {"cbor-zz", "cbor-a", "cbor-aa"},
              <<\hd9, \h01, \h02, \h83, \h66, \h63, \h62, \h6f, \h72, \h2d, \h61, \h67, \h63, \h62, \h6f, \h72,
                \h2d, \h61, \h61, \h67, \h63, \h62, \h6f, \h72, \h2d, \h7a, \h7a>>)
ASSUME Golden("set-nested", {{}, {1}, {1, 2}, {2}},
              <<\hd9, \h01, \h02, \h84, \hd9, \h01, \h02, \h80, \hd9, \h01, \h02, \h81, \h01, \hd9, \h01, \h02,
                \h81, \h02, \hd9, \h01, \h02, \h82, \h01, \h02>>)
\* In the next three sets, and in "fcn-mixed", the encodings first differ at a byte that is 0x80
\* or more, which a comparison of signed bytes would order the other way.
ASSUME Golden("set-wide", {200, 24}, <<\hd9, \h01, \h02, \h82, \h18, \h18, \h18, \hc8>>)
ASSUME Golden("set-modelvalue", {MV, 1},
              <<\hd9, \h01, \h02, \h82, \h01, \hd8, \h27, \h6a, \h4d, \h6f, \h64, \h65, \h6c, \h56, \h61, \h6c,
                \h75, \h65>>)
ASSUME Golden("set-utf8", {EAcute, "zz"},
              <<\hd9, \h01, \h02, \h82, \h62, \h7a, \h7a, \h62, \hc3, \ha9>>)
ASSUME Golden("emptyset", {}, <<\hd9, \h01, \h02, \h80>>)
ASSUME Golden("interval", {1, 2, 3}, <<\hd9, \h01, \h02, \h83, \h01, \h02, \h03>>)
ASSUME Golden("seq", <<"a", "b">>, <<\h82, \h61, \h61, \h61, \h62>>)
ASSUME Golden("empty", <<>>, <<\h80>>)
ASSUME Golden("record", [cborzz |-> 1, cbora |-> 2, cboraa |-> 3],
              <<\ha3, \h65, \h63, \h62, \h6f, \h72, \h61, \h02, \h66, \h63, \h62, \h6f, \h72, \h61, \h61, \h03,
                \h66, \h63, \h62, \h6f, \h72, \h7a, \h7a, \h01>>)
ASSUME Golden("fcn-int", 0 :> "x" @@ 1 :> "y",
              <<\hd9, \h80, \he8, \h82, \h82, \h00, \h61, \h78, \h82, \h01, \h61, \h79>>)
ASSUME Golden("fcn-tuple", [t \in {<<1, 2>>, <<2, 1>>} |-> 3],
              <<\hd9, \h80, \he8, \h82, \h82, \h82, \h01, \h02, \h03, \h82, \h82, \h02, \h01, \h03>>)
ASSUME Golden("fcn-set", [s \in SUBSET {1} |-> Cardinality(s)],
              <<\hd9, \h80, \he8, \h82, \h82, \hd9, \h01, \h02, \h80, \h00, \h82, \hd9, \h01, \h02, \h81, \h01,
                \h01>>)
ASSUME Golden("fcn-record", [r \in [a : {1, 2}] |-> r.a],
              <<\hd9, \h80, \he8, \h82, \h82, \ha1, \h61, \h61, \h01, \h01, \h82, \ha1, \h61, \h61, \h02, \h02>>)
ASSUME Golden("fcn-modelvalue", [m \in {MV} |-> 0],
              <<\hd9, \h80, \he8, \h81, \h82, \hd8, \h27, \h6a, \h4d, \h6f, \h64, \h65, \h6c, \h56, \h61, \h6c,
                \h75, \h65, \h00>>)
ASSUME Golden("fcn-mixed", [x \in {MV, 1} |-> 0],
              <<\hd9, \h80, \he8, \h82, \h82, \h01, \h00, \h82, \hd8, \h27, \h6a, \h4d, \h6f, \h64, \h65, \h6c,
                \h56, \h61, \h6c, \h75, \h65, \h00>>)

LOCAL DumpedTrace ==
    LET s1 == [x |-> 0, y |-> {}]
        s2 == [x |-> 1, y |-> {MV}]
        loc == [beginLine |-> 5, beginColumn |-> 9, endLine |-> 5, endColumn |-> 33, module |-> "T"]
    IN [counterexample |-> [state  |-> {<<1, s1>>, <<2, s2>>},
                            action |-> {<< <<1, s1>>, [name |-> "Next", location |-> loc], <<2, s2>> >>}],
        vars |-> {"x", "y"}]

ASSUME Golden("trace", DumpedTrace,
              <<\ha2, \h64, \h76, \h61, \h72, \h73, \hd9, \h01, \h02, \h82, \h61, \h78, \h61, \h79, \h6e, \h63,
                \h6f, \h75, \h6e, \h74, \h65, \h72, \h65, \h78, \h61, \h6d, \h70, \h6c, \h65, \ha2, \h65, \h73,
                \h74, \h61, \h74, \h65, \hd9, \h01, \h02, \h82, \h82, \h01, \ha2, \h61, \h78, \h00, \h61, \h79,
                \hd9, \h01, \h02, \h80, \h82, \h02, \ha2, \h61, \h78, \h01, \h61, \h79, \hd9, \h01, \h02, \h81,
                \hd8, \h27, \h6a, \h4d, \h6f, \h64, \h65, \h6c, \h56, \h61, \h6c, \h75, \h65, \h66, \h61, \h63,
                \h74, \h69, \h6f, \h6e, \hd9, \h01, \h02, \h81, \h83, \h82, \h01, \ha2, \h61, \h78, \h00, \h61,
                \h79, \hd9, \h01, \h02, \h80, \ha2, \h64, \h6e, \h61, \h6d, \h65, \h64, \h4e, \h65, \h78, \h74,
                \h68, \h6c, \h6f, \h63, \h61, \h74, \h69, \h6f, \h6e, \ha5, \h66, \h6d, \h6f, \h64, \h75, \h6c,
                \h65, \h61, \h54, \h67, \h65, \h6e, \h64, \h4c, \h69, \h6e, \h65, \h05, \h69, \h62, \h65, \h67,
                \h69, \h6e, \h4c, \h69, \h6e, \h65, \h05, \h69, \h65, \h6e, \h64, \h43, \h6f, \h6c, \h75, \h6d,
                \h6e, \h18, \h21, \h6b, \h62, \h65, \h67, \h69, \h6e, \h43, \h6f, \h6c, \h75, \h6d, \h6e, \h09,
                \h82, \h02, \ha2, \h61, \h78, \h01, \h61, \h79, \hd9, \h01, \h02, \h81, \hd8, \h27, \h6a, \h4d,
                \h6f, \h64, \h65, \h6c, \h56, \h61, \h6c, \h75, \h65>>)

\* Non-ASCII strings enter as bytes, so this file stays ASCII. The fifth string is U+1F600,
\* which TLC holds as two UTF-16 code units.
ASSUME LET bytes == <<\h85, \h60, \h61, \h61, \h62, \hc3, \hbc, \h66, \he6, \h97, \ha5, \he6, \h9c, \hac, \h64, \hf0,
                      \h9f, \h98, \h80>>
           s == FromCBOR(bytes)
       IN /\ Golden("string", s, bytes)
          /\ AssertEq(<<s[1], s[2]>>, <<"", "a">>)
          /\ AssertEq(<<Len(s[3]), Len(s[4]), Len(s[5])>>, <<1, 2, 2>>)

\* The deepest nesting FromCBOR reads: 512 sequences, one inside the other.
ASSUME LET bytes == [i \in 1..512 |-> IF i < 512 THEN \h81 ELSE \h80]
       IN AssertEq(ToCBOR(FromCBOR(bytes)), bytes)

\* The bytes of the integer 0 inside n values, one inside the other, that each start with wrap.
\* A recursive operator cannot build values this deep: TLC's own evaluation overflows the stack.
LOCAL CBORNested(wrap, n) ==
    [i \in 1..(n * Len(wrap) + 1) |-> IF i > n * Len(wrap) THEN 0 ELSE wrap[((i - 1) % Len(wrap)) + 1]]
LOCAL CBORInSeq == <<\h81>>
LOCAL CBORInRecord == <<\ha1, \h61, \h61>>
LOCAL CBORInSet == <<\hd9, \h01, \h02, \h81>>
LOCAL CBORInFcn == <<\hd9, \h80, \he8, \h81, \h82, \h00>>

\* The deepest values ToCBOR writes. A tag is a data item, so a set takes two of the 512 levels
\* and a function that uses tag 33000 three.
ASSUME \A d \in {<<CBORInSeq, 511>>, <<CBORInRecord, 511>>, <<CBORInSet, 255>>, <<CBORInFcn, 170>>} :
          LET bytes == CBORNested(d[1], d[2]) IN AssertEq(ToCBOR(FromCBOR(bytes)), bytes)

-----------------------------------------------------------------------------

ASSUME SameBytes("seq", << <<"a", "b">>,
                           [i \in 1..2 |-> IF i = 1 THEN "a" ELSE "b"],
                           2 :> "b" @@ 1 :> "a",
                           Tail(<<"z", "a", "b">>) >>,
                 <<\h82, \h61, \h61, \h61, \h62>>)

\* JsonDeserialize reads {} as a record without fields.
ASSUME SameBytes("empty", << <<>>,
                             [x \in {} |-> x],
                             JsonDeserialize("tests/CBORTests/empty-object.json") >>,
                 <<\h80>>)

ASSUME SameBytes("record", << [cbora |-> 2, cboraa |-> 3, cborzz |-> 1],
                              "cbora" :> 2 @@ "cborzz" :> 1 @@ "cboraa" :> 3,
                              [f \in {"cborzz", "cbora", "cboraa"} |->
                                  CASE f = "cbora" -> 2 [] f = "cboraa" -> 3 [] OTHER -> 1] >>,
                 <<\ha3, \h65, \h63, \h62, \h6f, \h72, \h61, \h02, \h66, \h63, \h62, \h6f, \h72, \h61, \h61, \h03,
                   \h66, \h63, \h62, \h6f, \h72, \h7a, \h7a, \h01>>)

ASSUME SameBytes("interval", << {3, 1, 2},
                                1..3,
                                {x \in -5..5 : x > 0 /\ x < 4},
                                {1, 1, 2, 3, 2} >>,
                 <<\hd9, \h01, \h02, \h83, \h01, \h02, \h03>>)

ASSUME SameBytes("set", << {10, 100, 10, -1}, {x \in -1..100 : x \in {-1, 10, 100}} >>,
                 <<\hd9, \h01, \h02, \h83, \h0a, \h18, \h64, \h20>>)
ASSUME SameBytes("set-nested", << SUBSET {1, 2}, {{1}, {2}} \cup {{}, {1, 2}} >>,
                 <<\hd9, \h01, \h02, \h84, \hd9, \h01, \h02, \h80, \hd9, \h01, \h02, \h81, \h01, \hd9, \h01, \h02,
                   \h81, \h02, \hd9, \h01, \h02, \h82, \h01, \h02>>)
ASSUME SameBytes("emptyset", << 1..0, {x \in {1} : FALSE}, {1} \ {1} >>,
                 <<\hd9, \h01, \h02, \h80>>)
ASSUME SameBytes("fcn-int", << [x \in 0..1 |-> IF x = 0 THEN "x" ELSE "y"], 1 :> "y" @@ 0 :> "x" >>,
                 <<\hd9, \h80, \he8, \h82, \h82, \h00, \h61, \h78, \h82, \h01, \h61, \h79>>)
ASSUME SameBytes("fcn-tuple", << (<<2, 1>> :> 3) @@ (<<1, 2>> :> 3),
                                 [t \in ({1, 2} \X {1, 2}) \ {<<1, 1>>, <<2, 2>>} |-> 3] >>,
                 <<\hd9, \h80, \he8, \h82, \h82, \h82, \h01, \h02, \h03, \h82, \h82, \h02, \h01, \h03>>)

-----------------------------------------------------------------------------

LOCAL RoundTrips(v) == AssertEq(FromCBOR(ToCBOR(v)), v)

\* Re-encoding a decoded value gives the bytes it was decoded from.
LOCAL Stable(v) == AssertEq(ToCBOR(FromCBOR(ToCBOR(v))), ToCBOR(v))

LOCAL CBORSamples == <<
    -2147483647 - 1, 2147483647, "",
    {MV, 1},
    <<<<>>, {}>>,
    [x \in {<<>>} |-> 1],
    [p \in {1, 2} \X {"a", "b"} |-> p[1]],
    [f \in [{1, 2} -> {TRUE, FALSE}] |-> f[1] /\ f[2]],
    {[a |-> 1, b |-> {<<1, "x">>}], [a |-> 2, b |-> {}]},
    <<[c |-> <<>>], {{{}}}, 3 :> [d |-> MV]>>,
    {TLCModelValue("C_cbor1"), TLCModelValue("C_cbor2")}
>>

ASSUME \A i \in DOMAIN CBORSamples : RoundTrips(CBORSamples[i]) /\ Stable(CBORSamples[i])

ASSUME \A S \in SUBSET {-2147483647 - 1, -25, -1, 0, 23, 24, 2147483647} : RoundTrips(S)
ASSUME \A s \in UNION {[1..n -> {"", "a", "cbor-zz"}] : n \in 0..2} : RoundTrips(s)
ASSUME \A r \in [{"a", "b"} -> BOOLEAN] : RoundTrips(r)
ASSUME \A f \in [{0, 2} -> {"x", "y"}] : RoundTrips(f)
ASSUME \A f \in [SUBSET {1, 2} -> {0, 1}] : RoundTrips(f) /\ Stable(f)
ASSUME \A f \in [{<<1, 2>>, <<2, 1>>} -> BOOLEAN] : RoundTrips(f) /\ Stable(f)
ASSUME \A f \in [{[a |-> 1], [a |-> 2]} -> {1, 2}] : RoundTrips(f)
ASSUME \A f \in [{MV, 1} -> {MV, "s"}] : RoundTrips(f) /\ Stable(f)
ASSUME RoundTrips(SUBSET SUBSET {1, 2}) /\ Stable(SUBSET SUBSET {1, 2})
ASSUME RoundTrips(DumpedTrace) /\ Stable(DumpedTrace)

\* Decoded values are marked normalized, so their order must be TLC's: TLC finds an
\* element of a normalized set, and an argument of a normalized function with at
\* least 32 entries, by bisection.
ASSUME LET s == FromCBOR(<<\hd9, \h01, \h02, \h83, \h0a, \h20, \h18, \h64>>)
       IN /\ \A x \in {-1, 10, 100} : x \in s
          /\ 0 \notin s
ASSUME LET f == FromCBOR(ToCBOR([x \in 0..40 |-> -x])) IN \A x \in 0..40 : f[x] = -x
ASSUME LET t == FromCBOR(ToCBOR(DumpedTrace))
       IN /\ Cardinality(t.counterexample.state) = 2
          /\ \E p \in t.counterexample.state : p[1] = 2 /\ MV \in p[2].y
          /\ t.vars = {"x", "y"}
ASSUME LET f == FromCBOR(ToCBOR([t \in {<<1, 2>>, <<2, 1>>} |-> 3]))
       IN DOMAIN f = {<<1, 2>>, <<2, 1>>} /\ f[<<2, 1>>] = 3

-----------------------------------------------------------------------------

\* FromCBOR reads bytes that TLC never writes, and ToCBOR writes the value it read in the one
\* canonical form.
LOCAL Accepts(bytes, value) ==
    /\ AssertEq(FromCBOR(bytes), value)
    /\ AssertEq(ToCBOR(FromCBOR(bytes)), ToCBOR(value))

\* Set elements, map keys, and pairs in any order, including the length-first order of
\* cbor2's canonical=True.
ASSUME Accepts(<<\hd9, \h01, \h02, \h82, \h02, \h01>>, {1, 2})
ASSUME Accepts(<<\hd9, \h01, \h02, \h83, \h0a, \h20, \h18, \h64>>, {100, -1, 10})
ASSUME Accepts(<<\ha2, \h61, \h62, \h01, \h61, \h61, \h02>>, [a |-> 2, b |-> 1])
ASSUME Accepts(<<\hd9, \h80, \he8, \h82, \h82, \h02, \h01, \h82, \h01, \h00>>, <<0, 1>>)
\* Integers and lengths in a wider form than needed.
ASSUME Accepts(<<\h1b, \h00, \h00, \h00, \h00, \h00, \h00, \h00, \h01>>, 1)
ASSUME Accepts(<<\h98, \h01, \h78, \h01, \h61>>, <<"a">>)
\* Maps whose keys are not strings, as Python writes a dict.
ASSUME Accepts(<<\ha2, \h00, \h61, \h78, \h01, \h61, \h79>>, 0 :> "x" @@ 1 :> "y")
ASSUME Accepts(<<\ha2, \h01, \h61, \h61, \h02, \h61, \h62>>, <<"a", "b">>)
ASSUME Accepts(<<\ha1, \h82, \h01, \h02, \h03>>, <<1, 2>> :> 3)
\* Pairs that form a record, and the empty function as an empty map and as no pairs.
ASSUME Accepts(<<\hd9, \h80, \he8, \h81, \h82, \h61, \h61, \h01>>, [a |-> 1])
ASSUME Accepts(<<\ha0>>, <<>>)
ASSUME Accepts(<<\hd9, \h80, \he8, \h80>>, <<>>)

-----------------------------------------------------------------------------

\* CBORSerialize writes the bytes of ToCBOR and creates missing parent directories. The bytes
\* of "CBOR" read as text: 0x64, the head of a text string of four bytes, is the letter d.
ASSUME /\ CBORSerialize("build/cbor/a/b/c/text.cbor", "CBOR")
       /\ AssertEq(ToCBOR("CBOR"), <<\h64, \h43, \h42, \h4f, \h52>>)
       /\ AssertEq(FileText("build/cbor/a/b/c/text.cbor"), "dCBOR")

\* CBORDeserialize reads a file as FromCBOR reads its bytes.
ASSUME \A i \in DOMAIN CBORSamples :
          /\ CBORSerialize("build/cbor/roundtrip.cbor", CBORSamples[i])
          /\ AssertEq(CBORDeserialize("build/cbor/roundtrip.cbor"), FromCBOR(ToCBOR(CBORSamples[i])))

\* A shorter value replaces a longer one; leftover bytes would be rejected as trailing.
ASSUME /\ CBORSerialize("build/cbor/overwrite.cbor", 1..100)
       /\ CBORSerialize("build/cbor/overwrite.cbor", 0)
       /\ AssertEq(CBORDeserialize("build/cbor/overwrite.cbor"), 0)

-----------------------------------------------------------------------------

\* AssertError needs its message as a literal.

ASSUME AssertError("FromCBOR: the input ends inside a CBOR data item at byte 0.",
                   FromCBOR(<<>>))
\* An array of two items that holds one.
ASSUME AssertError("FromCBOR: the input ends inside a CBOR data item at byte 0.",
                   FromCBOR(<<\h82, \h01>>))
ASSUME AssertError("FromCBOR: the input ends inside a CBOR data item at byte 0.",
                   FromCBOR(<<\h1a, \h00, \h00>>))
\* An array that claims 2^31 - 1 items is refused before anything is allocated.
ASSUME AssertError("FromCBOR: the input ends inside a CBOR data item at byte 0.",
                   FromCBOR(<<\h9a, \h7f, \hff, \hff, \hff>>))
ASSUME AssertError("FromCBOR: there are bytes after the first CBOR data item at byte 1.",
                   FromCBOR(<<\h01, \h01>>))
\* The inner array claims the three bytes that the outer array still needs for its other items.
ASSUME AssertError("FromCBOR: the input ends inside a CBOR data item at byte 1.",
                   FromCBOR(<<\h84, \h83, \h00, \h00, \h00>>))
\* The offset names the innermost offending item.
ASSUME AssertError("FromCBOR: null has no TLA+ counterpart at byte 2.",
                   FromCBOR(<<\h82, \h01, \hf6>>))
ASSUME AssertError("FromCBOR: a floating-point number has no TLA+ counterpart at byte 0.",
                   FromCBOR(<<\hf9, \h3c, \h00>>))
ASSUME AssertError("FromCBOR: null has no TLA+ counterpart at byte 0.",
                   FromCBOR(<<\hf6>>))
ASSUME AssertError("FromCBOR: undefined has no TLA+ counterpart at byte 0.",
                   FromCBOR(<<\hf7>>))
ASSUME AssertError("FromCBOR: a simple value has no TLA+ counterpart at byte 0.",
                   FromCBOR(<<\hf0>>))
ASSUME AssertError("FromCBOR: a byte string has no TLA+ counterpart at byte 0.",
                   FromCBOR(<<\h41, \h00>>))
ASSUME AssertError("FromCBOR: indefinite-length items are not supported at byte 0.",
                   FromCBOR(<<\h9f, \h01, \hff>>))
ASSUME AssertError("FromCBOR: indefinite-length items are not supported at byte 0.",
                   FromCBOR(<<\h7f, \h61, \h61, \hff>>))
ASSUME AssertError("FromCBOR: the initial byte 0x1c is not well-formed at byte 0.",
                   FromCBOR(<<\h1c>>))
ASSUME AssertError("FromCBOR: the initial byte 0xff is not well-formed at byte 0.",
                   FromCBOR(<<\hff>>))
ASSUME AssertError("FromCBOR: tag 1 has no TLA+ counterpart at byte 0.",
                   FromCBOR(<<\hc1, \h00>>))
\* A bignum.
ASSUME AssertError("FromCBOR: tag 2 has no TLA+ counterpart at byte 0.",
                   FromCBOR(<<\hc2, \h41, \h01>>))
ASSUME AssertError("FromCBOR: tag 39 must enclose a text string at byte 0.",
                   FromCBOR(<<\hd8, \h27, \h01>>))
ASSUME AssertError("FromCBOR: tag 258 must enclose an array at byte 0.",
                   FromCBOR(<<\hd9, \h01, \h02, \ha0>>))
ASSUME AssertError("FromCBOR: tag 33000 must enclose an array of [key, value] arrays at byte 0.",
                   FromCBOR(<<\hd9, \h80, \he8, \ha0>>))
ASSUME AssertError("FromCBOR: tag 33000 must enclose an array of [key, value] arrays at byte 0.",
                   FromCBOR(<<\hd9, \h80, \he8, \h81, \h01>>))
ASSUME AssertError("FromCBOR: the integer 2147483648 is outside TLC's range -2147483648..2147483647 at byte 0.",
                   FromCBOR(<<\h1a, \h80, \h00, \h00, \h00>>))
ASSUME AssertError("FromCBOR: the integer -2147483649 is outside TLC's range -2147483648..2147483647 at byte 0.",
                   FromCBOR(<<\h3a, \h80, \h00, \h00, \h00>>))
ASSUME AssertError("FromCBOR: the integer 18446744073709551615 is outside TLC's range -2147483648..2147483647 at byte 0.",
                   FromCBOR(<<\h1b, \hff, \hff, \hff, \hff, \hff, \hff, \hff, \hff>>))
ASSUME AssertError("FromCBOR: the integer -18446744073709551616 is outside TLC's range -2147483648..2147483647 at byte 0.",
                   FromCBOR(<<\h3b, \hff, \hff, \hff, \hff, \hff, \hff, \hff, \hff>>))
ASSUME AssertError("FromCBOR: a text string is not valid UTF-8 at byte 0.",
                   FromCBOR(<<\h61, \hff>>))
\* U+D800 encoded as if it were a character.
ASSUME AssertError("FromCBOR: a text string is not valid UTF-8 at byte 0.",
                   FromCBOR(<<\h63, \hed, \ha0, \h80>>))
ASSUME AssertError("FromCBOR: the key \"a\" occurs twice at byte 0.",
                   FromCBOR(<<\ha2, \h61, \h61, \h01, \h61, \h61, \h02>>))
\* The second 1 is not in shortest form: duplicates are found by TLC equality, not by bytes.
ASSUME AssertError("FromCBOR: the element 1 occurs twice at byte 0.",
                   FromCBOR(<<\hd9, \h01, \h02, \h82, \h01, \h18, \h01>>))
\* An empty array and an empty map both denote the empty function.
ASSUME AssertError("FromCBOR: the element <<>> occurs twice at byte 0.",
                   FromCBOR(<<\hd9, \h01, \h02, \h82, \h80, \ha0>>))
ASSUME AssertError("FromCBOR: the key 0 occurs twice at byte 0.",
                   FromCBOR(<<\hd9, \h80, \he8, \h82, \h82, \h00, \h01, \h82, \h00, \h02>>))
ASSUME AssertError("FromCBOR: TLC cannot compare the elements 1 and \"a\" at byte 0.",
                   FromCBOR(<<\hd9, \h01, \h02, \h82, \h01, \h61, \h61>>))
ASSUME AssertError("FromCBOR: TLC cannot compare the keys 1 and \"a\" at byte 0.",
                   FromCBOR(<<\ha2, \h01, \h00, \h61, \h61, \h00>>))
ASSUME AssertError("FromCBOR: the model value p99 is not defined in the model at byte 0. Declare it in the .cfg or create it with TLCExt!TLCModelValue(\"p99\").",
                   FromCBOR(<<\hd8, \h27, \h63, \h70, \h39, \h39>>))
ASSUME AssertError("FromCBOR: data items are nested more than 512 deep at byte 512.",
                   FromCBOR([i \in 1..513 |-> IF i < 513 THEN \h81 ELSE \h80]))

ASSUME AssertError("The argument of FromCBOR should be a sequence of integers in 0..255, but instead it is:\n42",
                   FromCBOR(42))
ASSUME AssertError("The argument of FromCBOR should be a sequence of integers in 0..255, but instead it is:\n<<1, 256>>",
                   FromCBOR(<<1, 256>>))
ASSUME AssertError("The argument of FromCBOR should be a sequence of integers in 0..255, but instead it is:\n<<-1>>",
                   FromCBOR(<<-1>>))
ASSUME AssertError("The argument of FromCBOR should be a sequence of integers in 0..255, but instead it is:\n<<\"a\">>",
                   FromCBOR(<<"a">>))

\* The offending value is named even when it is nested.
ASSUME AssertError("ToCBOR cannot encode a special set constant:\nNat",
                   ToCBOR([a |-> {Nat}]))
ASSUME AssertError("ToCBOR cannot encode an infinite set:\nSUBSET Nat",
                   ToCBOR(SUBSET Nat))
ASSUME AssertError("ToCBOR cannot encode a function with the infinite domain:\nNat",
                   ToCBOR([x \in Nat |-> x]))
\* One level more than the deepest values: ToCBOR refuses what FromCBOR could not read back.
ASSUME AssertError("ToCBOR cannot encode a value nested more than 512 CBOR data items deep.",
                   ToCBOR(<<FromCBOR(CBORNested(CBORInSeq, 511))>>))
ASSUME AssertError("ToCBOR cannot encode a value nested more than 512 CBOR data items deep.",
                   ToCBOR([a |-> FromCBOR(CBORNested(CBORInRecord, 511))]))
ASSUME AssertError("ToCBOR cannot encode a value nested more than 512 CBOR data items deep.",
                   ToCBOR({FromCBOR(CBORNested(CBORInSet, 255))}))
ASSUME AssertError("ToCBOR cannot encode a value nested more than 512 CBOR data items deep.",
                   ToCBOR(0 :> FromCBOR(CBORNested(CBORInFcn, 170))))
ASSUME AssertError("FromCBOR: data items are nested more than 512 deep at byte 1024.",
                   FromCBOR(CBORNested(CBORInSet, 256)))
ASSUME AssertError("FromCBOR: data items are nested more than 512 deep at byte 1024.",
                   FromCBOR(CBORNested(CBORInFcn, 171)))
\* SubSeq cuts U+1F600 in half, leaving an unpaired surrogate that UTF-8 cannot carry.
ASSUME AssertError("ToCBOR cannot encode a string that contains an unpaired UTF-16 surrogate.",
                   ToCBOR(SubSeq(FromCBOR(<<\h64, \hf0, \h9f, \h98, \h80>>), 1, 1)))

ASSUME AssertError("CBORDeserialize could not read tests/CBORTests/missing.cbor: the file does not exist.",
                   CBORDeserialize("tests/CBORTests/missing.cbor"))
\* A decoding error names the file. The JSON text {} starts with 0x7b, the head of a text string
\* whose length takes the next eight bytes.
ASSUME AssertError("CBORDeserialize could not read tests/CBORTests/empty-object.json: the input ends inside a CBOR data item at byte 0.",
                   CBORDeserialize("tests/CBORTests/empty-object.json"))
ASSUME AssertError("The first argument of CBORSerialize should be a string, but instead it is:\n42",
                   CBORSerialize(42, 1))
ASSUME AssertError("The argument of CBORDeserialize should be a string, but instead it is:\n42",
                   CBORDeserialize(42))

\* A refused value leaves the existing file as it was.
ASSUME /\ CBORSerialize("build/cbor/refused.cbor", "CBOR")
       /\ AssertError("CBORSerialize cannot encode a special set constant:\nNat",
                      CBORSerialize("build/cbor/refused.cbor", <<"a", Nat>>))
       /\ AssertEq(FileText("build/cbor/refused.cbor"), "dCBOR")

=============================================================================
