------------------------- MODULE SVGTests -------------------------
EXTENDS SVG, Sequences, Naturals, TLC, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("SVGTests")

(******************************************************************************)
(* Test conversion of SVG element records to strings.                         *)
(*                                                                            *)
(* We aren't worried about using real SVG element names and attributes here,  *)
(* since the logic only deals with converting the TLA+ record representing    *)
(* the element into a string.  The particular names of elements and           *)
(* attributes aren't important.                                               *)
(******************************************************************************)

ASSUME(LET 
        elem == [name |-> "test", attrs |-> [a |-> "10"], children |-> <<>>, innerText |-> ""] 
        expected == "<test a='10'></test>" IN
        AssertEq(SVGElemToString(elem), expected))

\* Test empty 'attrs'.
ASSUME(LET 
        elem == [name |-> "test", attrs |-> <<>>, children |-> <<>>, innerText |-> ""] 
        expected == "<test></test>" IN
        AssertEq(SVGElemToString(elem), expected))

\* Specifying the 'attrs' value as a function instead of a record should also be allowed.
ASSUME(LET 
        elem == [name |-> "test", attrs |-> ("a" :> "10" @@ "b" :> "20"), children |-> <<>>, innerText |-> ""] 
        expected == "<test a='10' b='20'></test>" IN
        AssertEq(SVGElemToString(elem), expected))

\* Test an element with 1 child.
ASSUME(LET 
        child == [name |-> "child", attrs |-> [c |-> "10"], children |-> <<>>, innerText |-> ""]
        elem == [name |-> "test", attrs |-> [a |-> "10"], children |-> <<child>>, innerText |-> ""]
        expected == "<test a='10'><child c='10'></child></test>" IN
        AssertEq(SVGElemToString(elem), expected))

\* Specifying the children as a function instead a tuple should also be allowed.
ASSUME(LET 
        child == [name |-> "child", attrs |-> [c |-> "10"], children |-> <<>>, innerText |-> ""]
        elem == [name |-> "test", attrs |-> [a |-> "10"], children |-> (1 :> child), innerText |-> ""]
        expected == "<test a='10'><child c='10'></child></test>" IN
        AssertEq(SVGElemToString(elem), expected))

\* Test an element with multiple children.
ASSUME(LET 
        child1 == [name |-> "child1", attrs |-> [c1 |-> "10"], children |-> <<>>, innerText |-> ""]
        child2 == [name |-> "child2", attrs |-> [c2 |-> "10"], children |-> <<>>, innerText |-> ""]
        elem == [name |-> "test", attrs |-> [a |-> "10"], children |-> <<child1, child2>>, innerText |-> ""]
        expected == "<test a='10'><child1 c1='10'></child1><child2 c2='10'></child2></test>" IN
        AssertEq(SVGElemToString(elem), expected))

\* Test an element with 'innerText'.
ASSUME(LET 
        elem == [name |-> "test", attrs |-> [a |-> "10"], children |-> <<>>, innerText |-> "hello"]
        expected == "<test a='10'>hello</test>" IN
        AssertEq(SVGElemToString(elem), expected))

\* Test an element with both children and 'innerText'.
\* It is not really meaningful/useful to have both 'children' and 'innerText', but
\* but we test it anyway since it is allowed.
ASSUME(LET 
        child == [name |-> "child", attrs |-> [c |-> "10"], children |-> <<>>, innerText |-> ""]
        elem == [name |-> "test", attrs |-> [a |-> "10"], children |-> <<child>>, innerText |-> "hello"]
        expected == "<test a='10'>hello<child c='10'></child></test>" IN
        AssertEq(SVGElemToString(elem), expected))

(******************************************************************************)
(* Test production of SVG element objects.                                    *)
(******************************************************************************)

ASSUME(LET 
        elem == Line(0, 1, 2, 3, [fill |-> "red"]) 
        expected == [ name |-> "line", 
                       attrs |-> [x1 |-> "0", y1 |-> "1", x2 |-> "2", y2 |-> "3", fill |-> "red"], 
                      children |-> <<>>, 
                      innerText |-> ""] IN
        AssertEq(elem, expected))

ASSUME(LET 
        elem == Circle(5, 5, 10, [fill |-> "red"])
        expected == [ name |-> "circle", 
                      attrs |-> [cx |-> "5", cy |-> "5", r |-> "10", fill |-> "red"], 
                      children |-> <<>>, 
                      innerText |-> ""] IN
        AssertEq(elem, expected))

ASSUME(LET 
        elem == Rect(0, 1, 2, 3, [fill |-> "red"]) 
        expected == [ name |-> "rect", 
                       attrs |-> [x |-> "0", y |-> "1", width |-> "2", height |-> "3", fill |-> "red"], 
                      children |-> <<>>, 
                      innerText |-> ""] IN
        AssertEq(elem, expected))

ASSUME(LET 
        elem == Text(0, 1, "hello", [fill |-> "red"]) 
        expected == [ name |-> "text", 
                       attrs |-> [x |-> "0", y |-> "1", fill |-> "red"], 
                      children |-> <<>>, 
                      innerText |-> "hello"] IN
        AssertEq(elem, expected))

ASSUME(LET 
        child == Rect(0, 1, 2, 3, [fill |-> "red"])
        elem == Group(<<child>>, [fill |-> "blue"])
        expected == [ name |-> "g", 
                       attrs |-> [fill |-> "blue"], 
                      children |-> <<child>>, 
                      innerText |-> ""] IN
        AssertEq(elem, expected))
        
(******************************************************************************)
(* Test replacement of '_' in SVG attributes with '-' because dashes are      *)
(* invalid in TLA+ record names.                                              *)
(******************************************************************************)

ASSUME(LET 
        elem == Line(0, 1, 2, 3, [fill |-> "red", stroke_dasharray |-> "42"]) 
        expected == "<line fill='red' x1='0' y1='1' x2='2' y2='3' stroke-dasharray='42'></line>" IN
        AssertEq(SVGElemToString(elem), expected))

-----------------------------------------------------------------------------

ASSUME(
    LET M == 3
        RN[ n \in 0..M ] ==
            NodeOfRingNetwork(10, 10, 6, n, M)
    IN RN = ( 0 :> [x |-> 16, y |-> 10] @@ 
              1 :> [x |-> 7,  y |-> 15] @@
              2 :> [x |-> 6,  y |-> 4 ] @@
              3 :> [x |-> 16, y |-> 9 ] )
)

ASSUME(LET 
		elem == Text(0, 0, ToString(<<1,2,3>>), <<>>)
      IN
        AssertEq(SVGElemToString(elem), "<text x='0' y='0'>&lt;&lt;1, 2, 3&gt;&gt;</text>"))

(******************************************************************************)
(* Test SVGDoc operator                                                       *)
(******************************************************************************)

\* Test SVGDoc with basic elements and viewBox
ASSUME(LET 
        circle == Circle(50, 50, 20, [fill |-> "blue"])
        rect == Rect(10, 10, 30, 40, [fill |-> "red"])
        doc == SVGDoc(<<circle, rect>>, 0, 0, 100, 100, [width |-> "200", height |-> "200"])
        expected == [ name |-> "svg", 
                      attrs |-> ("xmlns:xlink" :> "http://www.w3.org/1999/xlink" @@
                                 "xmlns" :> "http://www.w3.org/2000/svg" @@
                                 "viewBox" :> "0 0 100 100" @@
                                 "width" :> "200" @@
                                 "height" :> "200"), 
                      children |-> <<<<circle, rect>>>>, 
                      innerText |-> ""] IN
        AssertEq(doc, expected))

\* Test SVGDoc with empty children and no additional attributes
ASSUME(LET 
        doc == SVGDoc(<<>>, 10, 20, 800, 600, <<>>)
        expected == [ name |-> "svg", 
                      attrs |-> ("xmlns:xlink" :> "http://www.w3.org/1999/xlink" @@
                                 "xmlns" :> "http://www.w3.org/2000/svg" @@
                                 "viewBox" :> "10 20 800 600"), 
                      children |-> <<<<>>>>, 
                      innerText |-> ""] IN
        AssertEq(doc, expected))

\* Test SVGDoc string conversion
ASSUME(LET 
        text == Text(25, 25, "Hello SVG", [fill |-> "green"])
        doc == SVGDoc(text, 0, 0, 50, 50, [id |-> "test-svg"])
        expectedString == "<svg id='test-svg' xmlns:xlink='http://www.w3.org/1999/xlink' xmlns='http://www.w3.org/2000/svg' viewBox='0 0 50 50'><text x='25' y='25' fill='green'>Hello SVG</text></svg>" IN
        AssertEq(SVGElemToString(doc), expectedString))

(******************************************************************************)
(* Test SVGSerialize operator                                                 *)
(******************************************************************************)

\* Test SVGSerialize creates a file (we can't directly test file creation in TLA+,
\* but we can test that the operator doesn't crash and returns the expected result)
ASSUME(LET 
        circle == Circle(25, 25, 15, [fill |-> "purple"])
        doc == SVGDoc(circle, 0, 0, 50, 50, [width |-> "100", height |-> "100"])
        result == SVGSerialize(doc, "test_frame_", 1) IN
        \* SVGSerialize should return TRUE if successful (based on IOUtils pattern)
        result.exitValue = 0)

\* Test SVGSerialize with different frame numbers
ASSUME(LET 
        line == Line(0, 0, 50, 50, "stroke" :> "black" @@ "stroke-width" :> "2")
        doc == SVGDoc(line, 0, 0, 50, 50, <<>>)
        result == SVGSerialize(doc, "animation_", 42) IN
        result.exitValue = 0)


=============================================================================
