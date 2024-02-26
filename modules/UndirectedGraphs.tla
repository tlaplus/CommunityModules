------------------------- MODULE UndirectedGraphs ----------------------------
(****************************************************************************)
(* Representation of undirected graphs in TLA+. In contrast to module       *)
(* Graphs, edges are represented as unordered pairs {a,b} of nodes, thus    *)
(* enforcing symmetry.                                                      *)
(****************************************************************************)
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Folds

IsUndirectedGraph(G) ==
   /\ G = [node |-> G.node, edge |-> G.edge]
   /\ \A e \in G.edge : \E a,b \in G.node : e = {a,b}

IsLoopFreeUndirectedGraph(G) ==
   /\ G = [node |-> G.node, edge |-> G.edge]
   /\ \A e \in G.edge : \E a,b \in G.node : a # b /\ e = {a,b}

UndirectedSubgraph(G) ==
   {H \in [node : SUBSET G.node, edge : SUBSET G.edge] : IsUndirectedGraph(H)}

-----------------------------------------------------------------------------
Path(G) == {p \in Seq(G.node) :
             /\ p # << >>
             /\ \A i \in 1..(Len(p)-1) : {p[i], p[i+1]} \in G.edge}

SimplePath(G) ==
    \* A simple path is a path with no repeated nodes.
    {p \in SeqOf(G.node, Cardinality(G.node)) :
             /\ p # << >>
             /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
             /\ \A i \in 1..(Len(p)-1) : {p[i], p[i+1]} \in G.edge}

(****************************************************************************)
(* Compute the connected components of an undirected graph: initially each  *)
(* node is in a component by itself, then iterate over the edges to merge   *)
(* the components related by the edge.                                      *)
(****************************************************************************)
ConnectedComponents(G) ==
   LET base == {{n} : n \in G.node}
       choice(E) == CHOOSE e \in E : TRUE
       firstNode(e) == CHOOSE a \in G.node : \E b \in G.node : e = {a,b}
       secondNode(e) == CHOOSE b \in G.node : e = {firstNode(e), b}
       nodesOfEdge(e) == <<firstNode(e), secondNode(e)>>
       merge(e, comps) ==
          LET compA == CHOOSE c \in comps : e[1] \in c
              compB == CHOOSE c \in comps : e[2] \in c
          IN  IF compA = compB THEN comps
              ELSE (comps \ {compA, compB}) \union {compA \union compB}
   IN MapThenFoldSet(merge, base, nodesOfEdge, choice, G.edge)

AreConnectedIn(m, n, G) ==
   \E comp \in ConnectedComponents(G) : m \in comp /\ n \in comp

IsStronglyConnected(G) == 
  Cardinality(ConnectedComponents(G)) = 1
=============================================================================
