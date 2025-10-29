------------------------------- MODULE Graphs ------------------------------- 
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Relation

IsDirectedGraph(G) ==
   /\ G = [node |-> G.node, edge |-> G.edge]
   /\ G.edge \subseteq (G.node \X G.node)

DirectedSubgraph(G) ==    
  {H \in [node : SUBSET G.node, edge : SUBSET (G.node \X G.node)] :
     IsDirectedGraph(H) /\ H.edge \subseteq G.edge}

Transpose(G) ==
    \* https://en.wikipedia.org/wiki/Transpose_graph
    [ edge |-> { <<e[2], e[1]>> : e \in G.edge }, 
      node |-> G.node] 

-----------------------------------------------------------------------------
IsUndirectedGraph(G) ==
   /\ IsDirectedGraph(G)
   /\ \A e \in G.edge : <<e[2], e[1]>> \in G.edge

UndirectedSubgraph(G) == {H \in DirectedSubgraph(G) : IsUndirectedGraph(H)}
-----------------------------------------------------------------------------
Path(G) == {p \in Seq(G.node) :
             /\ p # << >>
             /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge}

SimplePath(G) ==
    \* A simple path is a path with no repeated nodes.
    {p \in SeqOf(G.node, Cardinality(G.node)) :
             /\ p # << >>
             /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
             /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge}

AreConnectedIn(m, n, G) == 
  \E p \in SimplePath(G) : (p[1] = m) /\ (p[Len(p)] = n)

ConnectionsIn(G) ==
  \* Compute a Boolean matrix that indicates, for each pair of nodes,
  \* if there exists a path that links the two nodes. The computation,
  \* based on Warshall's algorithm, is much more efficient than the
  \* definition used in AreConnectedIn, and the result can be cached
  \* by TLC, avoiding recomputation.
  LET C[N \in SUBSET G.node] ==
      \* Matrix representing the existence of paths whose inner nodes
      \* (i.e., except for the source and the target) are all in the
      \* set of nodes N.
      IF N = {}
      THEN [m,n \in G.node |-> m = n \/ <<m,n>> \in G.edge]
      ELSE LET u == CHOOSE u \in N : TRUE
               Cu == C[N \ {u}]
           IN  [m,n \in G.node |-> \/ Cu[m,n]
                                   \/ Cu[m,u] /\ Cu[u,n]]
  IN  C[G.node]

IsStronglyConnected(G) == 
  \A m, n \in G.node : AreConnectedIn(m, n, G) 
-----------------------------------------------------------------------------
IsTreeWithRoot(G, r) ==
  /\ IsDirectedGraph(G)
  /\ \A e \in G.edge : /\ e[1] # r
                       /\ \A f \in G.edge : (e[1] = f[1]) => (e = f)
  /\ \A n \in G.node : AreConnectedIn(n, r, G)
-----------------------------------------------------------------------------
(*************************************************************)
(* Returns the union of two graphs.                          *)
(*                                                           *)
(* Example:                                                  *)
(*   G = [node |-> {1, 2}, edge |-> {<<1, 2>>}]              *)
(*   H = [node |-> {2, 3}, edge |-> {<<2, 3>>}]              *)
(*   GraphUnion(G, H)                                        *)
(*     = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}] *)
(*************************************************************)
GraphUnion(G, H) ==
    [node |-> G.node \union H.node, edge |-> G.edge \union H.edge]

(********************************************************************)
(* Checks whether the graph G is bipartite with partitions U and V. *)
(*                                                                  *)
(* Example:                                                         *)
(*   G = [node |-> {1, 2, 3, 4},                                    *)
(*        edge |-> {<<1, 2>>, <<2, 3>>, <<3, 4>>}]                  *)
(*   IsBipartiteWithPartitions(G, {1, 3}, {2, 4}) = TRUE            *)
(********************************************************************)
IsBipartiteWithPartitions(G, U, V) ==
    /\ U \cap V = {}
    /\ G.node \subseteq (U \cup V)
    /\ \A e \in G.edge: \/ e[1] \in U /\ e[2] \in V
                        \/ e[2] \in U /\ e[1] \in V

(**************************************************************************)
(* Checks whether the graph G contains a cycle.                           *)
(*                                                                        *)
(* Note: Relies on the definition of ConnectionsIn. Please note that this *)
(* operator is defined recursively.                                       *)
(**************************************************************************)
HasCycle(G) ==
    \/ \E n \in G.node: << n, n >> \in G.edge
    \/ \E m, n \in G.node:
        /\ m # n
        /\ ConnectionsIn(G)[m, n]
        /\ ConnectionsIn(G)[n, m]

(**************************************************************************)
(* Checks whether the directed graph G is a directed Acyclic Graph (DAG). *)
(**************************************************************************)
IsDag(G) ==
    /\ IsDirectedGraph(G)
    /\ ~HasCycle(G)

(**************************************************************************)
(* Returns the set of nodes that are immediate successors of node n in G. *)
(*                                                                        *)
(* Example:                                                               *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]              *)
(*   Successors(G, 1) = {2, 3}                                            *)
(**************************************************************************)
Successors(G, n) == {m \in G.node: << n, m >> \in G.edge}

(****************************************************************************)
(* Returns the set of nodes that are immediate successors of any node in S. *)
(*                                                                          *)
(* Example:                                                                 *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]                *)
(*   AllSuccessors(G, {1, 2}) = {2, 3}                                      *)
(****************************************************************************)
AllSuccessors(G, S) == UNION {Successors(G, n): n \in S}

(****************************************************************************)
(* Returns the set of nodes that are immediate predecessors of node n in G. *)
(*                                                                          *)
(* Example:                                                                 *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]                *)
(*   Predecessors(G, 1) = {2, 3}                                            *)
(****************************************************************************)
Predecessors(G, n) == {m \in G.node: << m, n >> \in G.edge}

(******************************************************************************)
(* Returns the set of nodes that are immediate predecessors of any node in S. *)
(*                                                                            *)
(* Example:                                                                   *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]                  *)
(*   AllPredecessors(G, {1, 2}) = {2, 3}                                      *)
(******************************************************************************)
AllPredecessors(G, S) == UNION {Predecessors(G, n): n \in S}

(***************************************************************************)
(* Returns the set of all nodes in graph G that have a path to node n.     *)
(*                                                                         *)
(* Example:                                                                *)
(*   G == [node |-> {1, 2, 3, 4}, edge |-> {<<4, 2>>, <<2, 1>>, <<3, 1>>}] *)
(*   Ancestors(G, 1) = {2, 3, 4}                                           *)
(***************************************************************************)
Ancestors(G, n) ==
  LET EdgeRelation ==
        [<<x, y>> \in G.node \X G.node |-> <<x, y>> \in G.edge]
  IN  { m \in G.node : TransitiveClosure(EdgeRelation, G.node)[m, n] }

(***************************************************************************)
(* Returns the set of all nodes in graph G that are reachable from node n *)
(*                                                                         *)
(* Example:                                                                *)
(*   G == [node |-> {1, 2, 3, 4}, edge |-> {<<4, 2>>, <<2, 1>>, <<3, 1>>}] *)
(*   Descendants(G, 4) = {1, 2}                                            *)
(***************************************************************************)
Descendants(G, n) ==
  LET EdgeRelation ==
        [<<x, y>> \in G.node \X G.node |-> <<x, y>> \in G.edge]
  IN  { m \in G.node : TransitiveClosure(EdgeRelation, G.node)[n, m] }

(*************************************************************)
(* Returns the in-degree of node n in directed graph G.      *)
(*                                                           *)
(* Example:                                                  *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}] *)
(*   InDegree(G, 1) = 2                                      *)
(*************************************************************)
InDegree(G, n) == Cardinality(Predecessors(G, n))

(*************************************************************)
(* Returns the out-degree of node n in directed graph G.     *)
(*                                                           *)
(* Example:                                                  *)
(*   G = [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}] *)
(*   OutDegree(G, 1) = 2                                     *)
(*************************************************************)
OutDegree(G, n) == Cardinality(Successors(G, n))

(***************************************)
(* Returns the set of root nodes of G. *)
(***************************************)
Roots(G) == {n \in G.node: Predecessors(G, n) = {}}

(***************************************)
(* Returns the set of leaf nodes of G. *)
(***************************************)
Leaves(G) == {n \in G.node: Successors(G, n) = {}}
-----------------------------------------------------------------------------
(*****************************************)
(* The graph with no nodes and no edges. *)
(*****************************************)
EmptyGraph == [node |-> {}, edge |-> {}]

(************************************************************************)
(* The set of all possible labeled directed graphs whose node set is S. *)
(*                                                                      *)
(* Example:                                                             *)
(*   Graphs({1, 2}) = {                                                 *)
(*     [node |-> {1, 2}, edge |-> {}],                                  *)
(*     [node |-> {1, 2}, edge |-> {<<1, 2>>}],                          *)
(*     [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}],                *)
(*     ...                                                              *)
(*   }                                                                  *)
(************************************************************************)
Graphs(S) == [node: {S}, edge: SUBSET (S \X S)]
=============================================================================
\* Modification History
\* Last modified Sun Mar 06 18:10:34 CET 2022 by Stephan Merz
\* Last modified Tue Dec 21 15:55:45 PST 2021 by Markus Kuppe
\* Created Tue Jun 18 11:44:08 PST 2002 by Leslie Lamport