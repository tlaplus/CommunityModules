----------------------------- MODULE SVG -----------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE Integers
LOCAL INSTANCE TLC
LOCAL INSTANCE FiniteSets

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
SVGElem(_name, _attrs, _children, _innerText) == 
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

(**************************************************************************)
(* Line element.  'x1', 'y1', 'x2', and 'y2' should be given as integers. *)
(**************************************************************************)
Line(x1, y1, x2, y2, attrs) == 
    LET svgAttrs == [x1 |-> ToString(x1), 
                     y1 |-> ToString(y1), 
                     x2 |-> ToString(x2),
                     y2 |-> ToString(y2)] IN
    SVGElem("line", Merge(svgAttrs, attrs), <<>>, "")

(**************************************************************************)
(* Circle element. 'cx', 'cy', and 'r' should be given as integers.       *)
(**************************************************************************)
Circle(cx, cy, r, attrs) == 
    LET svgAttrs == [cx |-> ToString(cx), 
                     cy |-> ToString(cy), 
                     r  |-> ToString(r)] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")

(**************************************************************************)
(* Rectangle element.  'x', 'y', 'w', and 'h' should be given as          *)
(* integers.                                                              *)
(**************************************************************************)
Rect(x, y, w, h, attrs) == 
    LET svgAttrs == [x      |-> ToString(x), 
                     y      |-> ToString(y), 
                     width  |-> ToString(w), 
                     height |-> ToString(h)] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

(**************************************************************************)
(* Text element.'x' and 'y' should be given as integers, and 'text' given *)
(* as a string.                                                           *)
(**************************************************************************)
Text(x, y, text, attrs) == 
    LET svgAttrs == [x |-> ToString(x), 
                     y |-> ToString(y)] IN
    SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 

(**************************************************************************)
(* Image element. 'x', 'y', 'width', and 'height' should be given as      *)
(* integers, and 'href' given as a string specifying the image source.    *)
(**************************************************************************)
Image(x, y, width, height, href, attrs) == 
    LET svgAttrs == ("xlink:href" :> href @@
                     "x"         :> ToString(x) @@
                     "y"         :> ToString(y) @@
                     "width"     :> ToString(width) @@
                     "height"    :> ToString(height)) IN
    SVGElem("image", Merge(svgAttrs, attrs), <<>>, "")

(**************************************************************************)
(* Group element.  'children' is a sequence of elements that will be      *)
(* contained in this group.                                               *)
(**************************************************************************)
Group(children, attrs) == 
    SVGElem("g", attrs, children, "")

(**************************************************************************)
(* Svg container.  'children' is a sequence of elements that will be      *)
(* contained in this svg container.                                       *)
(**************************************************************************)
Svg(children, attrs) == 
    SVGElem("svg", attrs, children, "")

(**************************************************************************)
(* Creates a complete SVG document with viewBox and additional attributes.*)
(*                                                                        *)
(* Parameters:                                                            *)
(*   children: A sequence of SVG elements to include in the document      *)
(*   vbX, vbY: The x,y coordinates of the top-left corner of the viewBox  *)
(*   vbW, vbH: The width and height of the viewBox                        *)
(*   attrs:    Additional attributes to merge with the SVG root element   *)
(*                                                                        *)
(* The viewBox defines the coordinate system and viewport dimensions for  *)
(* the SVG content. This is essential for proper scaling and positioning  *)
(* of elements within the document.                                       *)
(**************************************************************************)
SVGDoc(children, vbX, vbY, vbW, vbH, attrs) ==
    LET svgAttrs == ("xmlns:xlink" :> "http://www.w3.org/1999/xlink" @@
                     "xmlns"       :> "http://www.w3.org/2000/svg" @@
                     "viewBox" :> ToString(vbX) \o " " \o
                                  ToString(vbY) \o " " \o
                                  ToString(vbW) \o " " \o
                                  ToString(vbH)) IN
    Svg(<<children>>, Merge(svgAttrs, attrs))

(**************************************************************************)
(* Convert an SVG element record into its string representation.          *)
(*                                                                        *)
(* This operator is expected to be replaced by a Java module override.    *)
(* We do not implement it in pure TLA+ because doing non-trivial string   *)
(* manipulation in TLA+ is tedious.  Also, the performance of             *)
(* implementing this in TLA+ has been demonstrated to be prohibitively    *)
(* slow.                                                                  *)
(**************************************************************************)
SVGElemToString(elem) == 
    TRUE    

-------------------------------------------------------------------------------

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
NodeOfRingNetwork(cx, cy, r, n, m) ==
    [ x |-> 0, y |-> 0 ]

(**************************************************************************)
(* Example to layout a graph with the given Nodes and Edges:              *)
(*                                                                        *)
(*      Nodes == {"v1", "v2", "v3"}  \* v3 is not connected               *)
(*      Edges == {<<"v1", "v2">>, <<"v2", "v1">>}                         *)
(*      Graph == NodesOfDirectedMultiGraph(Nodes, Edges, [algo |-> ...])  *)
(*                                                                        *)
(*      RN[ n \in Nodes ] ==                                              *)
(*           LET c == Graph[n]                                            *)
(*               node == Rect(c.x, c.y, 23, 42, <<>>)                     *)
(*           IN Group(<<node>>,  <<>>)                                    *)
(*                                                                        *)
(* For this operator's actual definition, please consult the Java module  *)
(* override at:                                                           *)
(*         modules/tlc2/overrides/SVG.java#directedMultiGraph             *)
(**************************************************************************)
NodesOfDirectedMultiGraph(nodes, edges, options) ==
    CHOOSE f \in [ nodes -> [x: Int, y: Int] ]: TRUE

PointOnLine(from, to, segment) ==
    [x |-> from.x + ((to.x - from.x) \div segment), 
     y |-> from.y + ((to.y - from.y) \div segment)]

-------------------------------------------------------------------------------

(**************************************************************************)
(* Serializes an SVG element to a file on disk.                           *)
(*                                                                        *)
(* Parameters:                                                            *)
(*   svg:             The SVG element/document to serialize               *)
(*   frameNamePrefix: String prefix for the output filename               *)
(*   frameNumber:     Numeric identifier appended to create unique files  *)
(*                                                                        *)
(* Creates a file named "<frameNamePrefix><frameNumber>.svg" containing   *)
(* the serialized SVG content. This is useful for generating animation    *)
(* frames or saving visualization snapshots.                              *)
(*                                                                        *)
(* Example usage:                                                         *)
(*   SVGSerialize(SVGDoc(myElements, 0, 0, 800, 600, <<>>),               *)
(*                "svg_frame_", TLCGet("level"))                          *)
(*                                                                        *)
(* This creates files like: svg_frame_1.svg,                              *)
(*                          svg_frame_2.svg, etc.                         *)
(**************************************************************************)
SVGSerialize(svg, frameNamePrefix, frameNumber) ==
    LET IO == INSTANCE IOUtils IN
    IO!Serialize(
        SVGElemToString(svg),
        frameNamePrefix \o ToString(frameNumber) \o ".svg",
        [format |-> "TXT", charset |-> "UTF-8", 
         openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>])

=============================================================================
