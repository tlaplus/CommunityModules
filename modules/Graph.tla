A module for representing directed graphs. Unlike the example module in specifying systems,
This can represent graphs with unconnected nodes. To do that we store a structure with both the edges and the list of all nodes:

Graphs == [node: {Nodes}, edge: [Nodes \X Nodes -> BOOLEAN]]

Additional operators act as predicates: they return whether or not a passed in graph satisfies the predicate.
This means that you can create sets of graphs by using a set filter. To get all weakly-connected DAGs, you write

{g \in Graphs: Acyclic(g) /\ WeaklyConnected(g)}

------------------------------- MODULE Graph -------------------------------

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

LOCAL Last(seq) == seq[Len(seq)]

(***************************************************************************)
(* Without edge weights, any cycles in a sequence of edges is redundant So *)
(* we can safely optimize out all sequences that visit the same node twice *)
(* with the exception of the first one, in case it's a full cycle.         *)
(*                                                                         *)
(* TODO optimize this                                                      *)
(***************************************************************************)
LOCAL EdgeSeq(graph) ==
  LET unique_sequences(m) ==
      {seq \in [1..m -> graph.node]: \A i, j \in 1..Len(seq)-1: i /= j => seq[i] /= seq[j]}
  IN UNION {unique_sequences(m) : m \in 2..Cardinality(graph.node)+1} \* All edgeseqs need at least two nodes

LOCAL Pairs(Nodes) == Nodes \X Nodes

(***************************************************************************)
(* Set of all possible graphs between nodes.                               *)
(*                                                                         *)
(* \A g \in Graphs(Nodes): g.node = Nodes /\ g.edge \in [Pairs(Nodes) ->   *)
(* BOOLEAN]                                                                *)
(***************************************************************************)
Graphs(Nodes) == 
  LET
    all_edges == [Pairs(Nodes) -> BOOLEAN] 
    valid_edges ==
        {e \in all_edges: \A n \in Nodes: ~e[n, n]} \* No edges to self
  IN [
    node: {Nodes},
    edge: valid_edges
  ]

(***************************************************************************)
(* A subgraph can leave out edges that are in the supergraph, but not add  *)
(* any new ones.                                                           *)
(***************************************************************************)

Subgraph(sub, super) ==
  /\ sub.node \subseteq super.node
  /\ \A m, n \in sub.node:
    sub.edge[m, n] => super.edge[m, n]

(***************************************************************************)
(* edge[1,2] /\ edge[2, 3] /\ edge[3, 1] => ConnectedEdge[1, 1]            *)
(***************************************************************************)

ConnectedEdge(graph) == 
  LET F[<<x, y>> \in Pairs(graph.node)] ==
    \E path \in EdgeSeq(graph):
      /\ path[1] = x
      /\ Last(path) = y
      /\ \A i \in 1..Len(path)-1:
        graph.edge[path[i], path[i+1]]
  IN F

(* Is the graph undirected? *)
Undirected(graph) ==
  \A m, n \in graph.node: graph.edge[n, m] <=> graph.edge[m, n]
  
(* Is the graph a directed acyclic graph? *)
Acyclic(graph) ==
  LET edge == ConnectedEdge(graph)
  IN  \A n \in graph.node: ~edge[n, n]
 
(*
  Is the graph weakly connected? IE graph is not several disjoint graphs
*)
WeaklyConnected(graph) ==
  LET edge == ConnectedEdge(graph)
  IN \A m, n \in graph.node: m /= n => edge[m, n] \/ edge[n, m]

=============================================================================

TODO: for N nodes there are 2^2N graphs. This makes this intractable very quickly, like 1024 distinct 5-node graphs.
Probably needs a java overide.
