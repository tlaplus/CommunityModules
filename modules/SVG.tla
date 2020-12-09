----------------------------- MODULE SVG -----------------------------
EXTENDS Naturals, Sequences, SequencesExt, Integers, TLC, FiniteSets

(******************************************************************************)
(* Helper Operators                                                           *)
(******************************************************************************)

LOCAL Merge(r1, r2) == 
    (**************************************************************************)
    (* Merge two records.                                                     *)
    (*                                                                        *)
    (* If a field appears in both records, then the value from 'r1' is kept.  *)
    (**************************************************************************)
    LET D1 == DOMAIN r1 
        D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

LOCAL SVGElem(_name, _attrs, _children, _innerText) == 
    (**************************************************************************)
    (* SVG element constructor.                                               *)
    (*                                                                        *)
    (* An SVG element like:                                                   *)
    (*                                                                        *)
    (* [name |-> "elem", attrs |-> [k1 |-> "0", k2 |-> "1"], children |->     *)
    (* <<>>, innerText |-> ""]                                                *)
    (*                                                                        *)
    (* would represent the SVG element '<elem k1="0" k2="1"></elem>'          *)
    (**************************************************************************)
    [name       |-> _name, 
     attrs      |-> _attrs, 
     children   |-> _children,
     innerText  |-> _innerText ]

(******************************************************************************)
(*                                                                            *)
(* Core Graphic Elements.                                                     *)
(*                                                                            *)
(* These primitives are TLA+ wrappers around SVG elements.  We base them on   *)
(* SVG since it is a widely used format and provides good features for        *)
(* representing and laying out vector graphics.  Each primitive below should  *)
(* roughly correspond to a standard SVG element type.  We represent a graphic *)
(* element as a record with the fields 'name', 'attrs', 'children', and       *)
(* 'innerText'.  'name' is the name of the SVG element, 'attrs' is a record   *)
(* mapping SVG attribute names to values, 'children' is a tuple containing    *)
(* any children elements, and 'innerText' is a string that represents any raw *)
(* text that is contained directly inside the SVG element.  The 'innerText'   *)
(* field is only meaningful for text elements.                                *)
(*                                                                            *)
(* All elements accept an 'attrs' argument, which must be a function mapping  *)
(* string keys to string values.  These key-value pairs describe any          *)
(* additional SVG attributes of the element.  To pass no attributes, just     *)
(* pass attrs=<<>>.                                                           *)
(*                                                                            *)
(******************************************************************************)

Line(x1, y1, x2, y2, attrs) == 
    (**************************************************************************)
    (* Line element.  'x1', 'y1', 'x2', and 'y2' should be given as integers. *)
    (**************************************************************************)
    LET svgAttrs == [x1 |-> ToString(x1), 
                     y1 |-> ToString(y1), 
                     x2 |-> ToString(x2),
                     y2 |-> ToString(y2)] IN
    SVGElem("line", Merge(svgAttrs, attrs), <<>>, "")

Circle(cx, cy, r, attrs) == 
    (**************************************************************************)
    (* Circle element. 'cx', 'cy', and 'r' should be given as integers.       *)
    (**************************************************************************)
    LET svgAttrs == [cx |-> ToString(cx), 
                     cy |-> ToString(cy), 
                     r  |-> ToString(r)] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")

Rect(x, y, w, h, attrs) == 
    (**************************************************************************)
    (* Rectangle element.  'x', 'y', 'w', and 'h' should be given as          *)
    (* integers.                                                              *)
    (**************************************************************************)
    LET svgAttrs == [x      |-> ToString(x), 
                     y      |-> ToString(y), 
                     width  |-> ToString(w), 
                     height |-> ToString(h)] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Text(x, y, text, attrs) == 
    (**************************************************************************)
    (* Text element.'x' and 'y' should be given as integers, and 'text' given *)
    (* as a string.                                                           *)
    (**************************************************************************)
    LET svgAttrs == [x |-> ToString(x), 
                     y |-> ToString(y)] IN
    SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 

Group(children, attrs) == 
    (**************************************************************************)
    (* Group element.  'children' is a sequence of elements that will be      *)
    (* contained in this group.                                               *)
    (**************************************************************************)
    SVGElem("g", attrs, children, "")

Svg(children, attrs) == 
    (**************************************************************************)
    (* Svg container.  'children' is a sequence of elements that will be      *)
    (* contained in this svg container.                                       *)
    (**************************************************************************)
    SVGElem("svg", attrs, children, "")

SVGElemToString(elem) == 
    (**************************************************************************)
    (* Convert an SVG element record into its string representation.          *)
    (*                                                                        *)
    (* This operator is expected to be replaced by a Java module override.    *)
    (* We do not implement it in pure TLA+ because doing non-trivial string   *)
    (* manipulation in TLA+ is tedious.  Also, the performance of             *)
    (* implementing this in TLA+ has been demonstrated to be prohibitively    *)
    (* slow.                                                                  *)
    (**************************************************************************)
    TRUE

-------------------------------------------------------------------------------

NodeOfRingNetwork(cx, cy, r, n, m) ==
    (**************************************************************************)
    (* Equals the Cartesian coordinates of the n-th of m nodes in a ring      *)
    (* (https://en.wikipedia.org/wiki/Ring_network), such that the circle     *)
    (* on which the nodes are placed has radius r and is centered at the      *)
    (* coordinates cx, cy.                                                    *)
    (*                                                                        *)
    (* ASSUME /\ n \in 0..360 /\ m \in 0..360 /\ n <= m                       *)
    (*        /\ cx \in Nat /\ cy \in Nat /\ r \in Nat                        *)
    (*                                                                        *)
    (* Example to create a ring network of M nodes (Rects with dimension 15)  *)
    (* with center (10,10) and radius 5:                                      *)
    (*                                                                        *)
    (*      ASSUME M \in Nat                                                  *)
    (*                                                                        *)
    (*      RN[ n \in 1..M ] ==                                               *)
    (*           LET c == NodeOfRingNetwork(10, 10, 5, n, M)                  *)
    (*               node == Rect(c.x, c.y, 15, 15, <<>>)                     *)
    (*           IN Group(<<node>>,  <<>>)                                    *)
    (*                                                                        *)
    (* Note: It would have been more elegant to provide the basic geometric   *)
    (*       operators, such as polar to Cartesian conversion.  However,      *)
    (*       TLC's lack of floats makes this impractical due to intermediate  *)
    (*       rounding errors.                                                 *)
    (*                                                                        *)
    (* For this operator's actual definition, please consult the Java module  *)
    (* override at:                                                           *)
    (*         modules/tlc2/overrides/SVG.java#ringNetwork                    *)
    (**************************************************************************)
    [ x |-> 0, y |-> 0 ]

=============================================================================
