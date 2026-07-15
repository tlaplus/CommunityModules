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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;

public final class UndirectedGraphs {

	private UndirectedGraphs() {
		// no-instantiation!
	}

	private static final StringValue NODE = new StringValue("node");
	private static final StringValue EDGE = new StringValue("edge");

	/*
	 * Validate that v is a graph record, i.e. a record with a "node" and an "edge"
	 * field, both of which are sets. Reporting the argument's position (e.g. "third"
	 * for AreConnectedIn) and rejecting malformed records here yields a proper
	 * user-facing TLC module argument error instead of a NullPointerException or
	 * ClassCastException later in nodes/adjacency.
	 */
	private static RecordValue toGraph(final String op, final String argPos, final Value v) {
		final Value rcd = v.toRcd();
		if (!(rcd instanceof RecordValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { argPos, op, "undirected graph record with a node and an edge field", Values.ppr(v.toString()) });
		}
		final RecordValue g = (RecordValue) rcd;
		final Value node = g.select(NODE);
		if (node == null || node.toSetEnum() == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { argPos, op, "undirected graph record whose node field is a set", Values.ppr(v.toString()) });
		}
		final Value edge = g.select(EDGE);
		if (edge == null || edge.toSetEnum() == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { argPos, op, "undirected graph record whose edge field is a set", Values.ppr(v.toString()) });
		}
		return g;
	}

	private static SetEnumValue nodes(final RecordValue g) {
		final SetEnumValue nodes = (SetEnumValue) g.select(NODE).toSetEnum();
		nodes.normalize();
		return nodes;
	}

	private static SetEnumValue edges(final RecordValue g) {
		final SetEnumValue edges = (SetEnumValue) g.select(EDGE).toSetEnum();
		edges.normalize();
		return edges;
	}

	/*
	 * Adjacency list of the graph, restricted to edges whose endpoints are both
	 * elements of the node set. This mirrors the TLA+ definitions, in which any
	 * node on a path is drawn from G.node.
	 *
	 * The definitions test {p[i], p[i+1]} \in G.edge.
	 * Any element of G.edge that is not a set of one or two elements (e.g. {} or
	 * {u, v, x}) can therefore never match and contributes no edge, so it is
	 * skipped rather than mis-parsed or causing an out-of-bounds error.
	 */
	private static Map<Value, List<Value>> adjacency(final RecordValue g, final SetEnumValue nodes) {
		final Map<Value, List<Value>> adj = new HashMap<>();
		final ValueEnumeration ve = edges(g).elements();
		Value v;
		while ((v = ve.nextElement()) != null) {
			final Value set = v.toSetEnum();
			if ((set == null) || !(set instanceof SetEnumValue)) {
				continue;
			}
			final SetEnumValue e = (SetEnumValue) set;
			if ((e.size() == 0) || (e.size() > 2)) {
				continue;
			}
			ValueEnumeration ne = e.elements();
			Value from = ne.nextElement();
			Value to = ne.nextElement();
			if (to == null) {
				to = from;
			}
			if (nodes.member(from) && nodes.member(to)) {
				// add the edges in both directions to enforce symmetry
				adj.computeIfAbsent(from, k -> new ArrayList<>()).add(to);
				if (from != to) {
					adj.computeIfAbsent(to, k -> new ArrayList<>()).add(from);
				}
			}
		}
		return adj;
	}

	/*
	 * SimplePath(G) ==
	 *     {p \in SeqOf(G.node, Cardinality(G.node)) :
	 *              /\ p # << >>
	 *              /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
	 *              /\ \A i \in 1..(Len(p)-1) : {p[i], p[i+1]} \in G.edge}
	 *
	 * Enumerates the set of all (non-empty) simple paths of G via depth-first
	 * search. This avoids materializing the (exponentially large) set
	 * SeqOf(G.node, Cardinality(G.node)) that the pure TLA+ definition ranges over.
	 */
	@TLAPlusOperator(identifier = "SimplePath", module = "UndirectedGraphs", warn = false)
	public static Value simplePath(final Value graph) {
		final RecordValue g = toGraph("SimplePath", "first", graph);
		final SetEnumValue nodes = nodes(g);
		final Map<Value, List<Value>> adj = adjacency(g, nodes);

		final List<Value> paths = new ArrayList<>();
		final List<Value> path = new ArrayList<>();
		final Set<Value> visited = new HashSet<>();
		final ValueEnumeration ve = nodes.elements();
		Value start;
		while ((start = ve.nextElement()) != null) {
			path.add(start);
			visited.add(start);
			extendSimplePath(start, adj, path, visited, paths);
			visited.remove(start);
			path.remove(path.size() - 1);
		}

		return new SetEnumValue(paths.toArray(new Value[paths.size()]), false);
	}

	// Backtracking depth-first search: emit the current path, then recurse into
	// each unvisited successor.
	private static void extendSimplePath(final Value current, final Map<Value, List<Value>> adj,
			final List<Value> path, final Set<Value> visited, final List<Value> paths) {
		// Every non-empty prefix of a simple path is itself a simple path.
		paths.add(new TupleValue(path.toArray(new Value[path.size()])));
		for (final Value succ : adj.getOrDefault(current, Collections.emptyList())) {
			if (visited.add(succ)) {
				path.add(succ);
				extendSimplePath(succ, adj, path, visited, paths);
				path.remove(path.size() - 1);
				visited.remove(succ);
			}
		}
	}

	/*
	 * AreConnectedIn(m, n, G) ==
	 *   \E p \in SimplePath(G) : (p[1] = m) /\ (p[Len(p)] = n)
	 *
	 * There is a simple (hence any) directed path from m to n. Note that <<m>> is a
	 * simple path, so a node is connected to itself iff it is a node of G.
	 */
	@TLAPlusOperator(identifier = "AreConnectedIn", module = "UndirectedGraphs", warn = false)
	public static Value areConnectedIn(final Value m, final Value n, final Value graph) {
		final RecordValue g = toGraph("AreConnectedIn", "third", graph);
		final SetEnumValue nodes = nodes(g);

		// Every node on a simple path is drawn from G.node, so m and n must both be
		// nodes. Checking membership first also matches the pure definition on an
		// empty node set: the existential domain SimplePath(G) is empty, hence the
		// result is FALSE and no comparison of m and n happens. Comparing m and n
		// up front (via the self-connection fast path below) would instead raise a
		// type error for incompatible arguments, e.g. AreConnectedIn(1, "x", G).
		if (!nodes.member(m) || !nodes.member(n)) {
			return BoolValue.ValFalse;
		}
		if (m.equals(n)) {
			return BoolValue.ValTrue;
		}

		final Map<Value, List<Value>> adj = adjacency(g, nodes);
		return reachable(m, adj).contains(n) ? BoolValue.ValTrue : BoolValue.ValFalse;
	}

	// Breadth-first search returning all nodes reachable from source (inclusive).
	private static Set<Value> reachable(final Value source, final Map<Value, List<Value>> adj) {
		final Set<Value> visited = new HashSet<>();
		final Deque<Value> frontier = new ArrayDeque<>();
		visited.add(source);
		frontier.add(source);
		while (!frontier.isEmpty()) {
			final Value current = frontier.remove();
			for (final Value succ : adj.getOrDefault(current, Collections.emptyList())) {
				if (visited.add(succ)) {
					frontier.add(succ);
				}
			}
		}
		return visited;
	}

	/*
	 * Compute the strongly connected components of an undirected graph: initially
	 * each node is in a component by itself, then iterate over the edges to merge
	 * the components related by the edge.
	 */
	@TLAPlusOperator(identifier = "ConnectedComponents", module = "UndirectedGraphs", warn = false)
	public static Value connectedComponents(final Value graph) {
		final RecordValue g = toGraph("ConnectedComponents", "first", graph);
		final SetEnumValue nds = nodes(g);
		final UnionFind comps = new UnionFind(nds.elements());

		final ValueEnumeration ee = edges(g).elements();
		Value edge;
		while ((edge = ee.nextElement()) != null) {
			final Value set = edge.toSetEnum();
			// ignore any "edges" that are not sets
			if ((set == null) || !(set instanceof SetEnumValue)) {
				continue;
			}
			final SetEnumValue e = (SetEnumValue) set;
			if (e.size() == 2) {
				// ignore singletons because doesn't merge any components
				final ValueEnumeration ve = e.elements();
				final Value from = ve.nextElement();
				final Value to = ve.nextElement();
				if (nds.member(from) && nds.member(to)) {
					// ignore any "edges" that do not relate two nodes
					comps.union(from, to);
				}
			}
		}

		// finally convert the UnionFind structure to a set of sets
		Map<Value, SetEnumValue> compSet = new LinkedHashMap<>();
		final ValueEnumeration ve = nds.elements();
		Value nd;
		while ((nd = ve.nextElement()) != null) {
			final Value rep = comps.find(nd);
			if (compSet.containsKey(rep)) {
				// add the current node to the component represented by rep
				SetEnumValue comp = compSet.get(rep);
				Value newcomp = comp.cup(new SetEnumValue(nd)).toSetEnum();
				if (newcomp instanceof SetEnumValue) {
					// why wouldn't this be the case? what to do then?
					compSet.put(rep, (SetEnumValue)newcomp);
				}
			} else {
				// put the singleton {rep} in the component map
				compSet.put(rep, new SetEnumValue(nd));
			}
		}
		SetEnumValue result = new SetEnumValue();
		for (SetEnumValue c : compSet.values()) {
			Value nr = result.cup(new SetEnumValue(c)).toSetEnum();
			if (nr instanceof SetEnumValue) {
				// how could this not be true?
				result = (SetEnumValue)nr;
			}
		}
		return result;
	}

	/*
	 * Helper class: union-find algorithm, used for computing SCCs.
	 */
	final static class UnionFind {
		private final Map<Value, Value> parent;  // map every value to its parent
		private int count;  // number of components

		/*
		 * Initialize a new union-find structure containing all values in elts
		 * as singleton components.
		 */
		public UnionFind(ValueEnumeration elts) {
			parent = new LinkedHashMap<>();
			count = 0;
			Value elt;
			while ((elt = elts.nextElement()) != null) {
				parent.put(elt, elt);  // initially every element is its own parent
				count++;
			}
		}

		/*
		 * Return the representative element of the component to which the element belongs.
		 * As a side effect, flatten the representation of the component.
		 */
		public Value find(final Value elt) {
			if (!(parent.containsKey(elt))) {
				throw new IllegalArgumentException("element not contained in UnionFind data structure: " + elt);
			}
			Value curr = elt;
			while (true) {
				Value par = parent.get(curr);
				if (par.equals(curr)) {
					break;
				}
				curr = par;
			}
			final Value root = curr;

			curr = elt;
			while (!curr.equals(root)) {
				Value par = parent.get(curr);
				parent.put(curr, root);
				curr = par;
			}

			return root;
		}

		/*
		 * Merge the components containing two elements.
		 */
		public void union(Value elt1, Value elt2) {
			if (!(parent.containsKey(elt1)) || !(parent.containsKey(elt2))) {
				throw new IllegalArgumentException("UnionFind data structure does not contain both " + elt1 +" and " + elt2);
			}

			Value par1 = find(elt1);
			Value par2 = find(elt2);

			if (!(par1.equals(par2))) {
				// nothing to do if the elements already belong to the same component
				parent.put(par2, par1);
				count--;
			}
		}
	}

}
