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

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import tlc2.tool.EvalControl;
import tlc2.value.impl.Applicable;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;

public class VectorClocks {

	private static class GraphNode {

		private final Set<GraphNode> parents = new HashSet<>();
		private final Set<GraphNode> children = new HashSet<>();

		private final Value value;
		private final Value clock;
		private final Enumerable domain;
		private final Value time;

		public GraphNode(final Value clock, final Value time, final Enumerable domain, Value value) {
			this.clock = clock;
			this.time = time;
			this.domain = domain;
			this.value = value;
		}

		public Value getClock() {
			return clock;
		}

		public Value getTime() {
			return time;
		}

		public Enumerable getHosts() {
			return domain;
		}

		public boolean hasParents() {
			return !parents.isEmpty();
		}

		public void addParent(GraphNode p) {
			this.parents.add(p);
			p.children.add(this);
		}

		public Value delete() {
			// Remove this node from its children, i.e., reduce the in-degree of this node's
			// children by one.
			this.children.forEach(g -> g.parents.remove(this));
			return value;
		}
	}

	/*
	 * The implementation is inspired by (MIT licensed) ShiViz. Specifically:
	 * https://github.com/DistributedClocks/shiviz/blob/
	 * ff02d48ed2bcda065f326aa25409cb317be9feb9/js/model/modelGraph.js
	 */
	@TLAPlusOperator(identifier = "CausalOrder", module = "VectorClocks", warn = false)
	public static Value causalOrder(final TupleValue v, final Applicable opClock, final Applicable opNode,
			final Applicable opDomain) {

		// A1) Sort each node's individual log which can be totally ordered.
		final Map<Value, LinkedList<GraphNode>> n2l = new HashMap<>();
		for (int j = 0; j < v.elems.length; j++) {
			final Value val = v.elems[j];

			final Value nodeId = opNode.apply(new Value[] { val }, EvalControl.Clear);
			final Value vc = opClock.apply(new Value[] { val }, EvalControl.Clear);
			final Value nodeTime = vc.select(new Value[] { nodeId });
			final Enumerable dom = (Enumerable) opDomain.apply(new Value[] { vc }, EvalControl.Clear).toSetEnum();

			final LinkedList<GraphNode> list = n2l.computeIfAbsent(nodeId, k -> new LinkedList<GraphNode>());
			list.add(new GraphNode(vc, nodeTime, dom, val));
		}

		// A2) Totally order each node's vector clocks in the log! They are likely
		// already be ordered, because a single process is unlike to have its log
		// reordered.
		n2l.values().forEach(list -> list.sort(new Comparator<GraphNode>() {
			@Override
			public int compare(GraphNode o1, GraphNode o2) {
				// It suffices the compare the node's vector clock value because a node's vector
				// clock value is incremented on every receive: "Each time a process receives a
				// message, it increments its own logical clock in the vector by one and ...'
				return o1.getTime().compareTo(o2.getTime());
			}
		}));

		// ----------------------------------------------------------------------- //

		// B) Merge the totally ordered logs into a directed acyclic graph (DAG).
		for (Value host : n2l.keySet()) {
			final LinkedList<GraphNode> list = n2l.get(host);

			// Initialize the global vector clock.
			final Map<Value, Value> globalClock = new HashMap<>();
			n2l.keySet().forEach(h -> globalClock.put(h, IntValue.ValZero));

			for (int i = 0; i < list.size(); i++) {
				final GraphNode gn = list.get(i);

				globalClock.put(host, gn.getTime());

				final Value c = gn.getClock();
				final ValueEnumeration hosts = gn.getHosts().elements();
				Value otherHost = null;
		        while ((otherHost = hosts.nextElement()) != null) {
					final Value time = c.select(new Value[] { otherHost });

					if (globalClock.get(otherHost).compareTo(time) < 0) {
						globalClock.put(otherHost, time);
						int idx = ((IntValue) time).val - 1;
						gn.addParent(n2l.get(otherHost).get(idx));
					}
				}
			}
		}

		// ----------------------------------------------------------------------- //

		// C) Pop one of the DAG's roots (zero in-degree) and append it to the list. We
		// know that at least one head of lists will be a root.
		final List<Value> sorted = new ArrayList<>(v.elems.length);
		int i = 0;
		while (i++ < v.elems.length) {
			for (Value host : n2l.keySet()) {
				final LinkedList<GraphNode> list = n2l.get(host);
				if (list.isEmpty()) {
					continue;
				}
				if (!list.peek().hasParents()) {
					final GraphNode g = list.remove();
					sorted.add(g.delete());
				}
			}
		}
		assert sorted.size() == v.elems.length;
		return new TupleValue(sorted.toArray(new Value[sorted.size()]));
	}
}
