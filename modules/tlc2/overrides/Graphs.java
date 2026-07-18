/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corporation. All rights reserved.
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

import java.util.List;
import java.util.Map;

import tlc2.value.impl.BoolValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;

/*
 * TLC overrides for the (directed) Graphs module.  Edges are ordered 2-tuples
 * <<from, to>>.  The bulk of the implementation is shared with UndirectedGraphs
 * via AbstractGraphs; this class only supplies the directed edge parser and the
 * operator entry points.
 */
public final class Graphs extends AbstractGraphs {

	private Graphs() {
		// no-instantiation!
	}

	private static final String KIND = "graph";

	/*
	 * The definitions test <<p[i], p[i+1]>> \in G.edge, i.e. membership of an exact
	 * 2-tuple.  Any element of G.edge that is not a 2-tuple (e.g. <<u>> or
	 * <<u, v, x>>) can therefore never match and contributes no edge, so it is
	 * skipped rather than mis-parsed (as u -> v) or causing an out-of-bounds error.
	 */
	private static final Endpoints TUPLE = edge -> {
		final Value tuple = edge.toTuple();
		if (!(tuple instanceof TupleValue) || ((TupleValue) tuple).size() != 2) {
			return null;
		}
		final TupleValue e = (TupleValue) tuple;
		return new Value[] { e.elems[0], e.elems[1] };
	};

	@TLAPlusOperator(identifier = "SimplePath", module = "Graphs", warn = false)
	public static Value simplePath(final Value graph) {
		return simplePath(KIND, TUPLE, Mode.FORWARD, graph);
	}

	@TLAPlusOperator(identifier = "AreConnectedIn", module = "Graphs", warn = false)
	public static Value areConnectedIn(final Value m, final Value n, final Value graph) {
		return areConnectedIn(KIND, TUPLE, Mode.FORWARD, m, n, graph);
	}

	/*
	 * IsStronglyConnected(G) == \A m, n \in G.node : AreConnectedIn(m, n, G)
	 *
	 * G is strongly connected iff, from an arbitrary node r, every node is reachable
	 * (forward) and r is reachable from every node (i.e., every node is reachable in
	 * the transposed graph).  This is the two-pass reachability test underlying
	 * Kosaraju's algorithm and runs in linear time instead of enumerating all pairs
	 * of nodes.
	 */
	@TLAPlusOperator(identifier = "IsStronglyConnected", module = "Graphs", warn = false)
	public static Value isStronglyConnected(final Value graph) {
		final RecordValue g = toGraph("IsStronglyConnected", "first", KIND, graph);
		final SetEnumValue nodes = nodes(g);

		final int order = nodes.size();
		if (order == 0) {
			return BoolValue.ValTrue;
		}

		final Value root = nodes.elements().nextElement();

		final Map<Value, List<Value>> adj = adjacency(g, nodes, TUPLE, Mode.FORWARD);
		if (reachable(root, adj).size() != order) {
			return BoolValue.ValFalse;
		}

		final Map<Value, List<Value>> radj = adjacency(g, nodes, TUPLE, Mode.TRANSPOSE);
		if (reachable(root, radj).size() != order) {
			return BoolValue.ValFalse;
		}

		return BoolValue.ValTrue;
	}
}
