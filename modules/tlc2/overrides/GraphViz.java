/*******************************************************************************
 * Copyright (c) 2023 Microsoft Research. All rights reserved.
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.overrides;

import tlc2.tool.EvalControl;
import tlc2.util.FP64;
import tlc2.value.impl.Applicable;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;

public class GraphViz {

	@TLAPlusOperator(identifier = "DotDiGraph", module = "GraphViz", warn = false)
	public static Value dotDiGraph(final Value v1, final Value v2, final Value v3) throws Exception {
		if (!(v1 instanceof RecordValue) || v1.toRcd() == null) {
			throw new Exception("An DiGraph must be a record. Value given is of type: " + v1.getClass().getName());
		}
		final RecordValue g = (RecordValue) v1.toRcd();

		if (!(v2 instanceof Applicable)) {
			throw new Exception(
					"Second parameter must be an Applicable. Value given is of type: " + v2.getClass().getName());
		}
		final Applicable vl = (Applicable) v2;

		if (!(v3 instanceof Applicable)) {
			throw new Exception(
					"Third parameter must be an Applicable. Value given is of type: " + v2.getClass().getName());
		}
		final Applicable el = (Applicable) v3;

		String dotString = "digraph MyGraph {";

		// Nodes
		// -3232796921283441800 [label="Some Node Label"];
		final SetEnumValue nodes = (SetEnumValue) g.select(new StringValue("node")).toSetEnum().normalize();
		ValueEnumeration elements = nodes.elements();
		Value val = null;
		while ((val = elements.nextElement()) != null) {
			dotString += String.format("%s[label=%s];", val.fingerPrint(FP64.New()),
					vl.apply(new Value[] { val }, EvalControl.Clear));
		}

		// Edges
		// -3232796921283441800 -> 2338507365925255731 [label="Some Edge Label"];
		final SetEnumValue edges = (SetEnumValue) g.select(new StringValue("edge")).toSetEnum().normalize();
		elements = edges.elements();
		while ((val = elements.nextElement()) != null) {
			TupleValue tv = (TupleValue) val.toTuple();
			dotString += String.format("%s->%s[label=%s];", tv.elems[0].fingerPrint(FP64.New()),
					tv.elems[1].fingerPrint(FP64.New()), el.apply(new Value[] { tv }, EvalControl.Clear));
		}

		dotString += "}";

		return new StringValue(dotString);
	}
}
