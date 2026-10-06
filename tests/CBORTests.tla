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
(* and the bytes that ToCBOR must return.  tests/CBORTests/fixtures.py, an *)
(* encoder that shares no code with CBOR.java, checks those bytes against  *)
(* its own encoding of the value it has under that name.                   *)
(*                                                                         *)
(* All definitions are LOCAL because AllTests extends every test module.   *)
(***************************************************************************)

LOCAL INSTANCE IOUtils
LOCAL INSTANCE Json

\* The model value that tests/AllTests.cfg defines, without redeclaring the
\* constant that JsonTests declares.
LOCAL MV == TLCModelValue("ModelValue")

LOCAL Golden(name, value, bytes) == AssertEq(ToCBOR(value), bytes)

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

\* CBORSerialize writes the bytes of ToCBOR and creates missing parent directories. The bytes
\* of "CBOR" read as text: 0x64, the head of a text string of four bytes, is the letter d.
ASSUME /\ CBORSerialize("build/cbor/a/b/c/text.cbor", "CBOR")
       /\ AssertEq(ToCBOR("CBOR"), <<\h64, \h43, \h42, \h4f, \h52>>)
       /\ AssertEq(FileText("build/cbor/a/b/c/text.cbor"), "dCBOR")

=============================================================================
