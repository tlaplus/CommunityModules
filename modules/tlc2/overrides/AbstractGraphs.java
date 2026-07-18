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
 *   Markus Alexander Kuppe - initial API and implementation
 *   Stephan Merz - undirected graphs
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

/*
 * Shared implementation of the TLC module overrides for the Graphs and
 * UndirectedGraphs modules.  The two graph kinds differ only in how an element
 * of G.edge denotes a pair of endpoints (an ordered 2-tuple for directed graphs
 * versus an unordered pair {a,b} for undirected graphs) and in whether the
 * resulting adjacency relation is symmetric.  Subclasses supply those two aspects
 * as an Endpoints delegate and a Mode; everything else (argument validation,
 * adjacency construction, path enumeration and reachability) is shared here.
 *
 * All members are static: subclasses inherit these helpers and call them,
 * passing their own edge parser.  The class is abstract only to prevent
 * instantiation and to give the two override classes a common home.
 */
public abstract class AbstractGraphs {

	protected AbstractGraphs() {
		// no-instantiation!
	}

	protected static final StringValue NODE = new StringValue("node");
	protected static final StringValue EDGE = new StringValue("edge");

	/*
	 * Parses one element of G.edge into its two endpoints {from, to}, or returns
	 * null if the value cannot denote an edge (and is therefore ignored).  A
	 * self-loop is returned as {n, n}.
	 */
	@FunctionalInterface
	protected interface Endpoints {
		Value[] of(Value edge);
	}

	/*
	 * How the arcs of the adjacency relation are derived from an edge's endpoints:
	 * FORWARD keeps the edge's orientation, TRANSPOSE reverses it, and SYMMETRIC
	 * adds both orientations.
	 */
	protected enum Mode {
		FORWARD, TRANSPOSE, SYMMETRIC
	}

	/*
	 * Validate that v is a graph record, i.e. a record with a "node" and an "edge"
	 * field, both of which are sets.  Reporting the argument's position (e.g. "third"
	 * for AreConnectedIn) and rejecting malformed records here yields a proper
	 * user-facing TLC module argument error instead of a NullPointerException or
	 * ClassCastException later in nodes/adjacency.  The kind noun (e.g. "graph" or
	 * "undirected graph") tailors the message to the calling module.
	 */
	protected static RecordValue toGraph(final String op, final String argPos, final String kind, final Value v) {
		final Value rcd = v.toRcd();
		if (!(rcd instanceof RecordValue)) {
			throw argError(op, argPos, kind, "record with a node and an edge field", v);
		}
		final RecordValue g = (RecordValue) rcd;
		final Value node = g.select(NODE);
		if (node == null || node.toSetEnum() == null) {
			throw argError(op, argPos, kind, "record whose node field is a set", v);
		}
		final Value edge = g.select(EDGE);
		if (edge == null || edge.toSetEnum() == null) {
			throw argError(op, argPos, kind, "record whose edge field is a set", v);
		}
		return g;
	}

	private static EvalException argError(final String op, final String argPos, final String kind,
			final String detail, final Value v) {
		return new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
				new String[] { argPos, op, kind + " " + detail, Values.ppr(v.toString()) });
	}

	protected static SetEnumValue nodes(final RecordValue g) {
		final SetEnumValue nodes = (SetEnumValue) g.select(NODE).toSetEnum();
		nodes.normalize();
		return nodes;
	}

	protected static SetEnumValue edges(final RecordValue g) {
		final SetEnumValue edges = (SetEnumValue) g.select(EDGE).toSetEnum();
		edges.normalize();
		return edges;
	}

	/*
	 * Adjacency list of the graph, restricted to edges whose endpoints are both
	 * elements of the node set.  This mirrors the TLA+ definitions, in which any
	 * node on a path is drawn from G.node.  Edges that the parser cannot handle
	 * (e.g. a tuple of the wrong arity, or a set of zero or more than two elements)
	 * contribute no arc and are skipped.
	 */
	protected static Map<Value, List<Value>> adjacency(final RecordValue g, final SetEnumValue nodes,
			final Endpoints parser, final Mode mode) {
		final Map<Value, List<Value>> adj = new HashMap<>();
		final ValueEnumeration ve = edges(g).elements();
		Value v;
		while ((v = ve.nextElement()) != null) {
			final Value[] e = parser.of(v);
			if (e == null) {
				continue;
			}
			Value from = e[0];
			Value to = e[1];
			if (!nodes.member(from) || !nodes.member(to)) {
				continue;
			}
			if (mode == Mode.TRANSPOSE) {
				final Value tmp = from;
				from = to;
				to = tmp;
			}
			addArc(adj, from, to);
			if (mode == Mode.SYMMETRIC && !from.equals(to)) {
				addArc(adj, to, from);
			}
		}
		return adj;
	}

	private static void addArc(final Map<Value, List<Value>> adj, final Value from, final Value to) {
		adj.computeIfAbsent(from, k -> new ArrayList<>()).add(to);
	}

	// Breadth-first search returning all nodes reachable from source (inclusive).
	protected static Set<Value> reachable(final Value source, final Map<Value, List<Value>> adj) {
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
	 * SimplePath(G) == { p \in Path(G) : \A i,j \in 1..Len(p) : p[i] = p[j] => i = j }
	 *
	 * Enumerates the set of all (non-empty) simple paths of G via depth-first
	 * search.  This avoids materializing the (infinite) set Path(G) that the pure
	 * TLA+ definition ranges over.
	 */
	protected static Value simplePath(final String kind, final Endpoints parser, final Mode mode, final Value graph) {
		final RecordValue g = toGraph("SimplePath", "first", kind, graph);
		final SetEnumValue nodes = nodes(g);
		final Map<Value, List<Value>> adj = adjacency(g, nodes, parser, mode);

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
	// each unvisited successor.  Every non-empty prefix of a simple path is itself
	// a simple path.
	private static void extendSimplePath(final Value current, final Map<Value, List<Value>> adj,
			final List<Value> path, final Set<Value> visited, final List<Value> paths) {
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
	 * AreConnectedIn(m, n, G) == \E p \in Path(G) : (p[1] = m) /\ (p[Len(p)] = n)
	 *
	 * There is a path from m to n.  Note that <<m>> is a path, so a node is
	 * connected to itself iff it is a node of G.
	 */
	protected static Value areConnectedIn(final String kind, final Endpoints parser, final Mode mode,
			final Value m, final Value n, final Value graph) {
		final RecordValue g = toGraph("AreConnectedIn", "third", kind, graph);
		final SetEnumValue nodes = nodes(g);

		// Every node on a path is drawn from G.node, so m and n must both be nodes.
		// Checking membership first also matches the pure definition on an empty node
		// set: the existential domain Path(G) is empty, hence the result is FALSE and
		// no comparison of m and n happens.  Comparing m and n up front (via the
		// self-connection fast path below) would instead raise a type error for
		// incompatible arguments, e.g. AreConnectedIn(1, "x", G).
		if (!nodes.member(m) || !nodes.member(n)) {
			return BoolValue.ValFalse;
		}
		if (m.equals(n)) {
			return BoolValue.ValTrue;
		}

		final Map<Value, List<Value>> adj = adjacency(g, nodes, parser, mode);
		return reachable(m, adj).contains(n) ? BoolValue.ValTrue : BoolValue.ValFalse;
	}
}
