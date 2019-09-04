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
    
MakeFrame(elem) == 
    (******************************************************************************)
    (* Builds a single frame for part of a sequence of animation frames.  This is *)
    (* an SVG group element that contains identifying information about the       *)
    (* frame.                                                                     *)
    (******************************************************************************)
    SVGElemToString(Group(<<elem>>, [class |-> "tlaframe"]))

=============================================================================