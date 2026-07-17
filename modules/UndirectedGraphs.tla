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
LOCAL INSTANCE Functions

IsUndirectedGraph(G) ==
   /\ G = [node |-> G.node, edge |-> G.edge]
   /\ \A e \in G.edge : \E a,b \in G.node : e = {a,b}

IsLoopFreeUndirectedGraph(G) ==
   /\ G = [node |-> G.node, edge |-> G.edge]
   /\ \A e \in G.edge : \E a,b \in G.node : a # b /\ e = {a,b}

UndirectedSubgraph(G) ==
   {H \in [node : SUBSET G.node, edge : SUBSET G.edge] : IsUndirectedGraph(H)}

-----------------------------------------------------------------------------
(****************************************************************************)
(* A path in a graph is a non-empty sequence of nodes connected by edges.   *)
(* A simple path is a path that does not contain duplicate nodes.           *)
(* Two nodes m and n are connected if there exists a path from m to n.      *)
(* A graph is strongly connected if all of its nodes are connected.         *)
(****************************************************************************)
Path(G) == {p \in Seq(G.node) :
             /\ p # << >>
             /\ \A i \in 1..(Len(p)-1) : {p[i], p[i+1]} \in G.edge}

SimplePath(G) ==
  \* NB: TLC uses a Java override for this operator because
  \* it cannot enumerate the set Path(G).
  { p \in Path(G) : \A i,j \in 1..Len(p) : p[i] = p[j] => i = j }

AreConnectedIn(m, n, G) ==
  \* NB: TLC uses a Java override for this operator.
  \E p \in Path(G) : (p[1] = m) /\ (p[Len(p)] = n)

-----------------------------------------------------------------------------
(****************************************************************************)
(* The (maximal) connected components are the maximal non-empty subsets S   *)
(* of nodes such that any two nodes in the set are connected by a path that *)
(* only visits nodes in S.                                                  *)
(****************************************************************************)
ConnectedComponents(G) == 
    \* NB: TLC uses a Java override for this operator.
    LET IsCC(S) == /\ S # {}
                   /\ \A m,n \in S : \E p \in Seq(S) : 
                         /\ p # << >> 
                         /\ p[1] = m /\ p[Len(p)] = n 
                         /\ \A i \in 1 .. Len(p)-1 : {p[i], p[i+1]} \in G.edge
    IN  { S \in SUBSET G.node : 
            /\ IsCC(S)
            /\ \A T \in SUBSET G.node : S \subseteq T /\ S # T => ~ IsCC(T)
        }

IsStronglyConnected(G) == 
  Cardinality(ConnectedComponents(G)) = 1

-----------------------------------------------------------------------------
(****************************************************************************)
(* The set of all possible undirecteddirected graphs whose node set is S.   *)
(*                                                                          *)
(* Example:                                                                 *)
(*   UndirectedGraphs({1, 2}) = {                                           *)
(*     [node |-> {1, 2}, edge |-> {}],                                      *)
(*     [node |-> {1, 2}, edge |-> {{1}}],                                   *)
(*     [node |-> {1, 2}, edge |-> {{2}}],                                   *)
(*     [node |-> {1, 2}, edge |-> {{1,2}}],                                 *)
(*     [node |-> {1, 2}, edge |-> {{1}, {1,2}}],                            *)
(*     [node |-> {1, 2}, edge |-> {{2}, {1,2}}],                            *)
(*     [node |-> {1, 2}, edge |-> {{1}, {2}, {1,2}}],                       *)
(*   }                                                                      *)
(****************************************************************************)
UndirectedGraphs(S) == [node: {S}, edge: SUBSET { {s, t} : <<s,t>> \in S \X S }]
=============================================================================
