/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   William Schultz - initial API and implementation
 ******************************************************************************/
package tlc2.overrides;

import java.util.Map;
import java.util.stream.Collectors;

import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultGraphType;
import org.jgrapht.graph.builder.GraphTypeBuilder;
import org.jgrapht.util.SupplierUtil;
import org.jungrapht.visualization.layout.algorithms.EiglspergerLayoutAlgorithm;
import org.jungrapht.visualization.layout.algorithms.LayoutAlgorithm;
import org.jungrapht.visualization.layout.algorithms.SugiyamaLayoutAlgorithm;
import org.jungrapht.visualization.layout.algorithms.TreeLayoutAlgorithm;
import org.jungrapht.visualization.layout.algorithms.sugiyama.Layering;
import org.jungrapht.visualization.layout.model.LayoutModel;
import org.jungrapht.visualization.layout.model.Point;
import org.jungrapht.visualization.layout.model.Rectangle;

import tlc2.tool.EvalControl;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueVec;
import util.UniqueString;

public final class SVG {

	private SVG() {
		// no-instantiation!
	}

	/**
	 * Converts an SVG element to its string representation.
	 * 
	 * In TLA+, an SVG object must be represented as a record with the following format:
	 * 
	 * [ name 		|-> <string>
	 *	 attrs 		|-> <record>
	 *	 children 	|-> <tuple>
	 *	 innerText 	|-> <string> ]
	 */
	@TLAPlusOperator(identifier = "SVGElemToString", module = "SVG", warn = false)
	public static Value SVGElemToString(Value elem) throws Exception {
		if (!(elem instanceof RecordValue) || elem.toRcd() == null) {
			throw new Exception(
					"An SVG element must be a record. Value given is of type: " + elem.getClass().getName());
		}

		RecordValue frv = (RecordValue) elem.toRcd();

		// Get 'name'.
		StringValue nameVal = (StringValue) frv.apply(new StringValue("name"), 0);
		String name = nameVal.getVal().toString();

		// Get 'attrs'. We convert it to 'RecordValue' type, which we expect should always be possible.
		Value attrsVal = frv.apply(new StringValue("attrs"), 0);
		RecordValue attrs = (RecordValue)(attrsVal.toRcd());
		if(attrs == null){
			throw new Exception("Was unable to convert element to a record: " + attrsVal.toString());
		}
		String attrStr = "";
		for (UniqueString us : attrs.names) {
			attrStr += " ";
			attrStr += us.toString().replaceAll("_", "-");
			attrStr += "=";
			String v = ((StringValue) attrs.apply(new StringValue(us), 0)).getVal().toString();
			// Quote all SVG attribute values. Technically, attribute values in HTML
			// don't always need to be quoted, but we use quotes so we can handle all
			// possible values. We single quote them to play nice with TLC string formatting.
			attrStr += "'" + v + "'";
		}

		// Get 'children'. We convert it to a TupleValue, which we expect should
		// always be possible.
		Value childrenVal = frv.apply(new StringValue("children"), 0);
		Value[] children;
		if (childrenVal instanceof TupleValue) {
			TupleValue tv = (TupleValue) childrenVal.toTuple();
			children = tv.elems;
		} else if (childrenVal instanceof RecordValue) {
			RecordValue rv = (RecordValue) childrenVal.toRcd();
			children = rv.values;
		} else if (childrenVal instanceof FcnRcdValue) {
			FcnRcdValue fcv = (FcnRcdValue) childrenVal.toFcnRcd();
			children = fcv.values;
		} else {
			throw new Exception("Was unable to convert element to a tuple or (function) record: " + childrenVal.toString());
		}
		String childStr = "";
		for (Value child : children) {
			StringValue cv = (StringValue)SVGElemToString(child);
			childStr += cv.getVal().toString();
		}

		// Get 'innerText'.
		// This is raw text placed inside the current SVG element. For example, if
		// 'innerText' was "hello", then we would output an SVG element like:
		//
		// <elem>hello</elem>
		//
		// For SVG elements that are not of type <text>, text inside an element is not
		// rendered, so this property is only meaningful for <text> elements. It is expected
		// to be empty for all other element types, but since it's not rendered, we don't 
		// explicitly disallow it.
		StringValue innerTextVal = (StringValue) frv.apply(new StringValue("innerText"), 0);
		String innerText = innerTextVal.getVal().toString();
		// Make sure TLA+ tuples such as <<1,2,3>> get properly rendered.
		innerText = innerText.replaceAll("<<", "&lt;&lt;").replaceAll(">>", "&gt;&gt;");

		// Produce the SVG element string.
		String svg = String.format("<%s%s>", name, attrStr);
		svg += innerText;
		svg += childStr;
		svg += String.format("</%s>", name);
		return new StringValue(svg);
	}
	
	@TLAPlusOperator(identifier = "NodeOfRingNetwork", module = "SVG", warn = false)
	public static Value ringNetwork(IntValue cx, IntValue cy, IntValue r, IntValue n, IntValue m) throws Exception {
		// https://en.wikipedia.org/wiki/Polar_coordinate_system#Converting_between_polar_and_Cartesian_coordinates
		
		// Divide circle into equal segments.
		final double angle = (2.0 * Math.PI / m.val) * n.val;
		
		// Polar to Cartesian coordinates offset by (cx,cy).
		final int x = (int) (cx.val + r.val * Math.cos(angle));
		final int y = (int) (cy.val + r.val * Math.sin(angle));
		return new RecordValue(new UniqueString[] {UniqueString.of("x"), UniqueString.of("y")}, new Value[] {IntValue.gen(x), IntValue.gen(y)}, false);
	}
	
	@TLAPlusOperator(identifier = "NodesOfDirectedMultiGraph", module = "SVG", warn = false)
	public static Value directedMultiGraph(final Value n, final Value e, final Value o)
			throws Exception {
		if (!(n instanceof SetEnumValue) && n.toSetEnum() == null) {
			throw new Exception(
					"Nodes must be a set. Value given is of type: " + n.getClass().getName());
		}
		if (!(e instanceof SetEnumValue) && e.toSetEnum() == null) {
			throw new Exception(
					"Edges must be a set. Value given is of type: " + e.getClass().getName());
		}
		if (!(o instanceof RecordValue) && o.toRcd() == null) {
			throw new Exception(
					"Opts must be a record. Value given is of type: " + o.getClass().getName());
		}
		final SetEnumValue nodes = (SetEnumValue) n.toSetEnum();
		final SetEnumValue edges = (SetEnumValue) e.toSetEnum();
		final RecordValue opts = (RecordValue) o.toRcd();
		
		// https://jgrapht.org/guide/UserOverview#graph-structures
		final Graph<Value, Integer> graph = GraphTypeBuilder
				.<Value, Integer>forGraphType(DefaultGraphType.directedMultigraph())
				.edgeSupplier(SupplierUtil.createIntegerSupplier()).allowingSelfLoops(false).buildGraph();

		ValueVec elems = nodes.elems;
		for (int i = 0; i < elems.size(); i++) {
			graph.addVertex(elems.elementAt(i));
		}
		elems = edges.elems;
		for (int i = 0; i < elems.size(); i++) {
			TupleValue tuple = (TupleValue) elems.elementAt(i);
			graph.addEdge(tuple.elems[0], tuple.elems[1]);
		}

		// Layout
		final IntValue viewH = (IntValue) opts.apply(new StringValue("view_width"), EvalControl.Clear);
		final IntValue viewW = (IntValue) opts.apply(new StringValue("view_height"), EvalControl.Clear);
		final LayoutModel<Value> layoutModel = LayoutModel.<Value>builder().size(viewW.val, viewH.val).graph(graph)
				.build();

		// Algorithm
		final StringValue algo = (StringValue) opts.apply(new StringValue("algo"), EvalControl.Clear);
		getAlgo(algo.val.toString(), opts).visit(layoutModel);

		// Get the node's coordinates from the algorithm.
		final Map <Value, Point> locations = layoutModel.getLocations();
		
		// convert to TLC values.
		return new FcnRcdValue(locations.entrySet().stream()
				.collect(Collectors.toMap(entry -> entry.getKey(), entry -> point2Value(entry.getValue()))));
	}

	private static Value point2Value(final Point p) {
		final int x = ((Double) p.x).intValue();
		final int y = ((Double) p.y).intValue();
		return new RecordValue(new UniqueString[] { UniqueString.of("x"), UniqueString.of("y") },
				new Value[] { IntValue.gen(x), IntValue.gen(y) }, false);
	}

	private static LayoutAlgorithm<Value> getAlgo(final String algo, final RecordValue opts) {
		final IntValue nodeH = (IntValue) opts.apply(new StringValue("node_width"), EvalControl.Clear);
		final IntValue nodeW = (IntValue) opts.apply(new StringValue("node_height"), EvalControl.Clear);

		switch (algo) {
		case "Sugiyama":
			// https://github.com/tomnelson/jungrapht-visualization/blob/afd155bf0246e5185f054ba1429bbcfbd429292a/jungrapht-layout/src/main/java/org/jungrapht/visualization/layout/algorithms/sugiyama/Layering.java#L4-L7
			String l = ((StringValue) opts.apply(new StringValue("layering"), EvalControl.Clear)).val.toString();
			return SugiyamaLayoutAlgorithm.<Value, Integer>edgeAwareBuilder()
					.layering(Layering.valueOf(l)).vertexBoundsFunction(v -> Rectangle.of(-5, -5, nodeW.val, nodeH.val)).threaded(false)
					.build();
		case "Eiglsperger":
			l = ((StringValue) opts.apply(new StringValue("layering"), EvalControl.Clear)).val.toString();
			return EiglspergerLayoutAlgorithm.<Value, Integer>edgeAwareBuilder()
					.layering(Layering.valueOf(l)).vertexBoundsFunction(v -> Rectangle.of(-5, -5, nodeW.val, nodeH.val)).threaded(false)
					.build();
		default:
			return TreeLayoutAlgorithm.<Value>builder()
					.vertexBoundsFunction(v -> Rectangle.of(-5, -5, nodeW.val, nodeH.val)).build();
		}
	}
	
	@TLAPlusOperator(identifier = "PointOnLine", module = "SVG", warn = false)
	public static Value pointOnLine(final RecordValue from, final RecordValue to, final IntValue idx) throws Exception {
		int fx = ((IntValue) from.select(new StringValue("x"))).val;
		int fy = ((IntValue) from.select(new StringValue("y"))).val;
		
		int tx = ((IntValue) to.select(new StringValue("x"))).val;
		int ty = ((IntValue) to.select(new StringValue("y"))).val;

		int x = (int) (fx + ((tx - fx) / (idx.val * 1d)));
		int y = (int) (fy + ((ty - fy) / (idx.val * 1d)));
		
		return new RecordValue(new UniqueString[] {UniqueString.of("x"), UniqueString.of("y")}, new Value[] {IntValue.gen(x), IntValue.gen(y)}, false);
	}
}
