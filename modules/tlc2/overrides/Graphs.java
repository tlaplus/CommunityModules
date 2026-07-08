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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
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

public final class Graphs {

	private Graphs() {
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
					new String[] { argPos, op, "graph record with a node and an edge field", Values.ppr(v.toString()) });
		}
		final RecordValue g = (RecordValue) rcd;
		final Value node = g.select(NODE);
		if (node == null || node.toSetEnum() == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { argPos, op, "graph record whose node field is a set", Values.ppr(v.toString()) });
		}
		final Value edge = g.select(EDGE);
		if (edge == null || edge.toSetEnum() == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { argPos, op, "graph record whose edge field is a set", Values.ppr(v.toString()) });
		}
		return g;
	}

	private static SetEnumValue nodes(final RecordValue g) {
		final SetEnumValue nodes = (SetEnumValue) g.select(NODE).toSetEnum();
		nodes.normalize();
		return nodes;
	}

	/*
	 * Adjacency list of the graph, restricted to edges whose endpoints are both
	 * elements of the node set. This mirrors the TLA+ definitions, in which any
	 * node on a path is drawn from G.node.
	 *
	 * The definitions test <<p[i], p[i+1]>> \in G.edge, i.e. membership of an exact
	 * 2-tuple. Any element of G.edge that is not a 2-tuple (e.g. <<u>> or
	 * <<u, v, x>>) can therefore never match and contributes no edge, so it is
	 * skipped rather than mis-parsed (as u -> v) or causing an out-of-bounds error.
	 */
	private static Map<Value, List<Value>> adjacency(final RecordValue g, final SetEnumValue nodes,
			final boolean transpose) {
		final SetEnumValue edges = (SetEnumValue) g.select(EDGE).toSetEnum();
		final Map<Value, List<Value>> adj = new HashMap<>();
		final ValueEnumeration ve = edges.elements();
		Value v;
		while ((v = ve.nextElement()) != null) {
			final Value tuple = v.toTuple();
			if (!(tuple instanceof TupleValue) || ((TupleValue) tuple).size() != 2) {
				continue;
			}
			final TupleValue e = (TupleValue) tuple;
			Value from = e.elems[0];
			Value to = e.elems[1];
			if (transpose) {
				final Value tmp = from;
				from = to;
				to = tmp;
			}
			if (nodes.member(from) && nodes.member(to)) {
				adj.computeIfAbsent(from, k -> new ArrayList<>()).add(to);
			}
		}
		return adj;
	}

	/*
	 * SimplePath(G) ==
	 *     {p \in SeqOf(G.node, Cardinality(G.node)) :
	 *              /\ p # << >>
	 *              /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
	 *              /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge}
	 *
	 * Enumerates the set of all (non-empty) simple paths of G via depth-first
	 * search. This avoids materializing the (exponentially large) set
	 * SeqOf(G.node, Cardinality(G.node)) that the pure TLA+ definition ranges over.
	 */
	@TLAPlusOperator(identifier = "SimplePath", module = "Graphs", warn = false)
	public static Value simplePath(final Value graph) {
		final RecordValue g = toGraph("SimplePath", "first", graph);
		final SetEnumValue nodes = nodes(g);
		final Map<Value, List<Value>> adj = adjacency(g, nodes, false);

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
	@TLAPlusOperator(identifier = "AreConnectedIn", module = "Graphs", warn = false)
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

		final Map<Value, List<Value>> adj = adjacency(g, nodes, false);
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
	 * IsStronglyConnected(G) ==
	 *   \A m, n \in G.node : AreConnectedIn(m, n, G)
	 *
	 * G is strongly connected iff, from an arbitrary node r, every node is reachable
	 * (forward) and r is reachable from every node (i.e., every node is reachable in
	 * the transposed graph). This is the two-pass reachability test underlying
	 * Kosaraju's algorithm and runs in linear time instead of enumerating all pairs
	 * of nodes.
	 */
	@TLAPlusOperator(identifier = "IsStronglyConnected", module = "Graphs", warn = false)
	public static Value isStronglyConnected(final Value graph) {
		final RecordValue g = toGraph("IsStronglyConnected", "first", graph);
		final SetEnumValue nodes = nodes(g);

		final int order = nodes.size();
		if (order == 0) {
			return BoolValue.ValTrue;
		}

		final Value root = nodes.elements().nextElement();

		final Map<Value, List<Value>> adj = adjacency(g, nodes, false);
		if (reachable(root, adj).size() != order) {
			return BoolValue.ValFalse;
		}

		final Map<Value, List<Value>> radj = adjacency(g, nodes, true);
		if (reachable(root, radj).size() != order) {
			return BoolValue.ValFalse;
		}

		return BoolValue.ValTrue;
	}
}
