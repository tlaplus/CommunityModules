/*******************************************************************************
 * Copyright (c) 2026 TLA+ Foundation. All rights reserved.
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
 *   Stephan Merz - initial API and implementation (largely based on Graphs.java)
 ******************************************************************************/
package tlc2.overrides;

import java.util.LinkedHashMap;
import java.util.Map;

import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;

/*
 * TLC overrides for the UndirectedGraphs module.  Edges are unordered pairs, i.e.
 * sets {a, b} of one or two nodes.  SimplePath and AreConnectedIn are shared with
 * the directed Graphs module via AbstractGraphs; this class supplies the
 * undirected edge parser and the ConnectedComponents override.
 */
public final class UndirectedGraphs extends AbstractGraphs {

	private UndirectedGraphs() {
		// no-instantiation!
	}

	private static final String KIND = "undirected graph";

	/*
	 * The definitions test {p[i], p[i+1]} \in G.edge, i.e. membership of an unordered
	 * pair.  Any element of G.edge that is not a set of one or two elements (e.g. {}
	 * or {u, v, x}) can therefore never match and contributes no edge, so it is
	 * skipped.  A singleton {u} denotes the self-loop {u, u}.
	 */
	private static final Endpoints PAIR = edge -> {
		final Value set = edge.toSetEnum();
		if (!(set instanceof SetEnumValue)) {
			return null;
		}
		final SetEnumValue e = (SetEnumValue) set;
		if ((e.size() == 0) || (e.size() > 2)) {
			return null;
		}
		final ValueEnumeration ne = e.elements();
		final Value from = ne.nextElement();
		final Value to = ne.nextElement();
		return new Value[] { from, to == null ? from : to };
	};

	@TLAPlusOperator(identifier = "SimplePath", module = "UndirectedGraphs", warn = false)
	public static Value simplePath(final Value graph) {
		return simplePath(KIND, PAIR, Mode.SYMMETRIC, graph);
	}

	@TLAPlusOperator(identifier = "AreConnectedIn", module = "UndirectedGraphs", warn = false)
	public static Value areConnectedIn(final Value m, final Value n, final Value graph) {
		return areConnectedIn(KIND, PAIR, Mode.SYMMETRIC, m, n, graph);
	}

	/*
	 * Compute the connected components of an undirected graph: initially each node is
	 * in a component by itself, then iterate over the edges to merge the components
	 * related by an edge.  Self-loops (singleton edges) and edges with an endpoint
	 * outside the node set do not merge anything.
	 */
	@TLAPlusOperator(identifier = "ConnectedComponents", module = "UndirectedGraphs", warn = false)
	public static Value connectedComponents(final Value graph) {
		final RecordValue g = toGraph("ConnectedComponents", "first", KIND, graph);
		final SetEnumValue nds = nodes(g);
		final UnionFind comps = new UnionFind(nds.elements());

		final ValueEnumeration ee = edges(g).elements();
		Value edge;
		while ((edge = ee.nextElement()) != null) {
			final Value[] e = PAIR.of(edge);
			if (e == null) {
				continue;
			}
			if (nds.member(e[0]) && nds.member(e[1])) {
				comps.union(e[0], e[1]);
			}
		}

		// finally convert the UnionFind structure to a set of sets
		final Map<Value, SetEnumValue> compSet = new LinkedHashMap<>();
		final ValueEnumeration ve = nds.elements();
		Value nd;
		while ((nd = ve.nextElement()) != null) {
			final Value rep = comps.find(nd);
			if (compSet.containsKey(rep)) {
				// add the current node to the component represented by rep
				final SetEnumValue comp = compSet.get(rep);
				compSet.put(rep, (SetEnumValue) comp.cup(new SetEnumValue(nd)).toSetEnum());
			} else {
				// start a new component {nd}
				compSet.put(rep, new SetEnumValue(nd));
			}
		}
		SetEnumValue result = new SetEnumValue();
		for (final SetEnumValue c : compSet.values()) {
			result = (SetEnumValue) result.cup(new SetEnumValue(c)).toSetEnum();
		}
		return result;
	}

	/*
	 * Helper class: union-find algorithm, used for computing connected components.
	 */
	static final class UnionFind {
		private final Map<Value, Value> parent; // map every value to its parent
		private int count; // number of components

		/*
		 * Initialize a new union-find structure containing all values in elts as
		 * singleton components.
		 */
		public UnionFind(final ValueEnumeration elts) {
			parent = new LinkedHashMap<>();
			count = 0;
			Value elt;
			while ((elt = elts.nextElement()) != null) {
				parent.put(elt, elt); // initially every element is its own parent
				count++;
			}
		}

		/*
		 * Return the representative element of the component to which the element
		 * belongs. As a side effect, flatten the representation of the component.
		 */
		public Value find(final Value elt) {
			if (!(parent.containsKey(elt))) {
				throw new IllegalArgumentException("element not contained in UnionFind data structure: " + elt);
			}
			Value curr = elt;
			while (true) {
				final Value par = parent.get(curr);
				if (par.equals(curr)) {
					break;
				}
				curr = par;
			}
			final Value root = curr;

			curr = elt;
			while (!curr.equals(root)) {
				final Value par = parent.get(curr);
				parent.put(curr, root);
				curr = par;
			}

			return root;
		}

		/*
		 * Merge the components containing two elements.
		 */
		public void union(final Value elt1, final Value elt2) {
			if (!(parent.containsKey(elt1)) || !(parent.containsKey(elt2))) {
				throw new IllegalArgumentException(
						"UnionFind data structure does not contain both " + elt1 + " and " + elt2);
			}

			final Value par1 = find(elt1);
			final Value par2 = find(elt2);

			if (!(par1.equals(par2))) {
				// nothing to do if the elements already belong to the same component
				parent.put(par2, par1);
				count--;
			}
		}
	}
}
