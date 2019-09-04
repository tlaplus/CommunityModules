------------------------- MODULE SVGTests -------------------------
EXTENDS SVG, Sequences, Naturals, TLC

\* AssertEq(a, b) is logically equivalent to the expression 'a = b'. If a and b are not equal, 
\* however, AssertEq(a, b) will print out the values of 'a' and 'b'. If the two values are equal,
\* nothing will be printed.
AssertEq(a, b) == 
    IF a # b THEN
        /\ PrintT("Assertion failed")
        /\ PrintT(a)
        /\ PrintT(b)
        /\ a = b
    ELSE a = b

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

=============================================================================
