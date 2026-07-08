------------------------- MODULE GraphsTests -------------------------
EXTENDS Graphs, SequencesExt, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("GraphsTests")

(******************************************************************************)
(* Pure TLA+ reference definitions, kept verbatim in sync with the operators  *)
(* in modules/Graphs.tla. They serve as the oracle against which the Java     *)
(* module overrides (SimplePath, AreConnectedIn, IsStronglyConnected) are     *)
(* checked exhaustively below. ConnectionsIn (Warshall's algorithm) provides  *)
(* a second, independent oracle for reachability.                             *)
(******************************************************************************)
LOCAL SimplePathPure(G) ==
    {p \in SeqOf(G.node, Cardinality(G.node)) :
             /\ p # << >>
             /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
             /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge}

LOCAL AreConnectedInPure(m, n, G) ==
    \E p \in SimplePathPure(G) : (p[1] = m) /\ (p[Len(p)] = n)

LOCAL IsStronglyConnectedPure(G) ==
    \A m, n \in G.node : AreConnectedInPure(m, n, G)

\* One representative graph set of each node-set cardinality 0 through 3
\* (including the empty graph and self-loops). The operators treat nodes as
\* opaque values and are invariant under renaming, so a graph on nodes {1, 3}
\* or {2, 3} is just a relabeling of one on {1, 2} and adds no coverage. It
\* therefore suffices to use the prefixes {}, {1}, {1, 2}, {1, 2, 3} rather
\* than all same-cardinality node sets (e.g. Graphs({1, 3}), Graphs({2, 3})).
LOCAL SmallGraphs ==
    Graphs({}) \cup Graphs({1}) \cup Graphs({1, 2}) \cup Graphs({1, 2, 3})

(******************************************************************************)
(* A graph whose edge set is built via a set image that yields the same edge  *)
(* multiple times, i.e. a potentially non-normalized SetEnumValue. The        *)
(* overrides enumerate sets via SetEnumValue#elements(), which normalizes     *)
(* (deduplicates), so the result is unaffected by the input representation.   *)
(******************************************************************************)
LOCAL DupEdgeGraph ==
    [node |-> {1, 2, 3},
     edge |-> {<<2, 3>>} \cup { <<1, 2>> : i \in {"a", "b", "c"} }]

ASSUME AssertEq(Cardinality(SimplePath(DupEdgeGraph)), 6)
ASSUME AssertEq(SimplePath(DupEdgeGraph),
            {<<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>, <<1, 2, 3>>})

(******************************************************************************)
(* SimplePath Tests                                                           *)
(******************************************************************************)
ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {}]), {})
ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {1,2,3}]), {<<1>>, <<2>>, <<3>>})
ASSUME AssertEq(SimplePath([edge|-> {<<1,2>>, <<2,3>>}, node |-> {1,2,3}]), 
            { <<1>>, <<2>>, <<3>>, <<1,2>>, <<2,3>>, <<1,2,3>> } )

\* A self-loop never yields a path with a repeated node, so it does not add any
\* simple path beyond the single-node one.
ASSUME AssertEq(SimplePath([node |-> {1}, edge |-> {<<1, 1>>}]), {<<1>>})
ASSUME AssertEq(SimplePath([node |-> {1, 2}, edge |-> {<<1, 1>>, <<1, 2>>}]),
            {<<1>>, <<2>>, <<1, 2>>})

\* A 2-cycle contributes both directed edges as simple paths.
ASSUME AssertEq(SimplePath([node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}]),
            {<<1>>, <<2>>, <<1, 2>>, <<2, 1>>})

\* A 3-cycle contributes every rotation as a simple path.
ASSUME AssertEq(SimplePath([node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]),
            {<<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>, <<3, 1>>,
             <<1, 2, 3>>, <<2, 3, 1>>, <<3, 1, 2>>})

\* Exhaustively: the Java override agrees with the original TLA+ definition for
\* every directed graph in SmallGraphs.
ASSUME \A g \in SmallGraphs : AssertEq(SimplePath(g), SimplePathPure(g))

(******************************************************************************)
(* AreConnectedIn Tests                                                       *)
(******************************************************************************)
ASSUME \A g \in Graphs({"A", "B", "C"}):
    \A u,v \in g.node :
        AreConnectedIn(u, v, g) \in BOOLEAN 

\* A node is connected to itself iff it is a node of the graph (via <<n>>).
ASSUME AssertEq(AreConnectedIn(1, 1, [node |-> {1}, edge |-> {}]), TRUE)
ASSUME AssertEq(AreConnectedIn(1, 1, EmptyGraph), FALSE)

\* Connectivity is directed and requires both endpoints to be nodes of the graph.
ASSUME AssertEq(AreConnectedIn(1, 2, [node |-> {1, 2}, edge |-> {<<1, 2>>}]), TRUE)
ASSUME AssertEq(AreConnectedIn(2, 1, [node |-> {1, 2}, edge |-> {<<1, 2>>}]), FALSE)
ASSUME AssertEq(AreConnectedIn(1, 9, [node |-> {1, 2}, edge |-> {<<1, 2>>}]), FALSE)

ASSUME LET G ==  [node |-> {1,2,3,4,5,6}, 
                  edge |-> {<<1,2>>, <<2,3>>, <<2,4>>, <<3,2>>, <<3,4>>, <<3,5>>, 
                            <<4,2>>, <<5,6>>, <<6,5>>}]
       IN  \A m,n \in G.node : AreConnectedIn(m,n,G) <=> ConnectionsIn(G)[m,n]

\* Exhaustively: the override agrees with the original TLA+ definition and with
\* the independent ConnectionsIn oracle for every graph in SmallGraphs.
ASSUME \A g \in SmallGraphs :
    \A m, n \in g.node :
        /\ AreConnectedIn(m, n, g) = AreConnectedInPure(m, n, g)
        /\ AreConnectedIn(m, n, g) <=> ConnectionsIn(g)[m, n]

(******************************************************************************)
(* IsStronglyConnected Tests                                                  *)
(******************************************************************************)
ASSUME \A g \in Graphs({1, 2, 3}): IsStronglyConnected(g) \in BOOLEAN

\* The empty graph is (vacuously) strongly connected.
ASSUME AssertEq(IsStronglyConnected(EmptyGraph), TRUE)

\* A single node is strongly connected (a node is connected to itself via the
\* trivial path <<n>>), with or without a self-loop.
ASSUME AssertEq(IsStronglyConnected([node |-> {1}, edge |-> {}]), TRUE)
ASSUME AssertEq(IsStronglyConnected([node |-> {1}, edge |-> {<<1, 1>>}]), TRUE)

\* A simple directed cycle is strongly connected.
ASSUME AssertEq(IsStronglyConnected([node |-> {1, 2, 3},
                                     edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]), TRUE)

\* Two mutually connected nodes are strongly connected, ...
ASSUME AssertEq(IsStronglyConnected([node |-> {1, 2},
                                     edge |-> {<<1, 2>>, <<2, 1>>}]), TRUE)

\* ... whereas a single directed edge between them is not.
ASSUME AssertEq(IsStronglyConnected([node |-> {1, 2},
                                     edge |-> {<<1, 2>>}]), FALSE)

\* A directed line (path graph) is not strongly connected.
ASSUME AssertEq(IsStronglyConnected([node |-> {1, 2, 3},
                                     edge |-> {<<1, 2>>, <<2, 3>>}]), FALSE)

\* A graph with two separate strongly connected components is not strongly
\* connected as a whole.
ASSUME AssertEq(IsStronglyConnected([node |-> {1, 2, 3, 4},
                                     edge |-> {<<1, 2>>, <<2, 1>>,
                                               <<3, 4>>, <<4, 3>>}]), FALSE)

\* Exhaustively: the override agrees with the original TLA+ definition and with
\* the independent ConnectionsIn oracle for every graph in SmallGraphs.
ASSUME \A g \in SmallGraphs :
    /\ IsStronglyConnected(g) = IsStronglyConnectedPure(g)
    /\ IsStronglyConnected(g) <=> (\A m, n \in g.node : ConnectionsIn(g)[m, n])

(******************************************************************************)
(* Value identity Tests                                                       *)
(*                                                                            *)
(* These tests use composite node values (sets) that are written with         *)
(* different internal orderings but denote the same TLA+ value, so that nodes *)
(* and edge endpoints are matched by value equality rather than by their      *)
(* concrete representation.                                                   *)
(******************************************************************************)
ASSUME LET G == [node |-> {{1, 2}, {3}}, edge |-> {<<{1, 2}, {3}>>}]
       IN /\ AssertEq(SimplePath(G), {<<{1, 2}>>, <<{3}>>, <<{1, 2}, {3}>>})
          /\ AssertEq(AreConnectedIn({1, 2}, {3}, G), TRUE)
          /\ AssertEq(AreConnectedIn({3}, {1, 2}, G), FALSE)
          /\ AssertEq(IsStronglyConnected(G), FALSE)

\* The edge endpoint {2, 1} and the node/argument {1, 2} denote the same set, so
\* the override must treat them as identical despite the differing literal order.
ASSUME LET G == [node |-> {{1, 2}, {3}}, edge |-> {<<{2, 1}, {3}>>, <<{3}, {1, 2}>>}]
       IN /\ AssertEq(AreConnectedIn({1, 2}, {3}, G), TRUE)
          /\ AssertEq(AreConnectedIn({3}, {2, 1}, G), TRUE)
          /\ AssertEq(IsStronglyConnected(G), TRUE)

(******************************************************************************)
(* GraphUnion Tests                                                           *)
(******************************************************************************)
ASSUME LET G == [node |-> {1, 2}, edge |-> {<<1, 2>>}]
           H == [node |-> {2, 3}, edge |-> {<<2, 3>>}]
       IN AssertEq(GraphUnion(G, H),
                    [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])

(******************************************************************************)
(* IsBipartiteWithPartitions Tests                                            *)
(******************************************************************************)

ASSUME LET G == [node |-> {1, 2, 3, 4},
                 edge |-> {<<1, 2>>, <<2, 3>>, <<3, 4>>}]
       IN AssertEq(IsBipartiteWithPartitions(G, {1, 3}, {2, 4}), TRUE)

(******************************************************************************)
(* IsDag Tests                                                                *)
(******************************************************************************)
ASSUME \A g \in Graphs({1, 2, 3}): IsDag(g) \in BOOLEAN

ASSUME AssertEq(IsDag([node |-> {1, 2, 3, 4},
                       edge |-> {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>}]), TRUE)

ASSUME AssertEq(IsDag([node |-> {1},
                       edge |-> {<<1, 1>>}]), FALSE)

ASSUME AssertEq(IsDag([node |-> {1, 2},
                       edge |-> {<<1, 2>>, <<2, 1>>}]), FALSE)

ASSUME AssertEq(IsDag([node |-> {1, 2, 3},
                       edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]), FALSE)

ASSUME AssertEq(IsDag(EmptyGraph), TRUE)

(******************************************************************************)
(* Successors Tests                                                           *)
(******************************************************************************)
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]
       IN AssertEq(Successors(G, 1), {2, 3})

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]
       IN AssertEq(Successors(G, 2), {})

(******************************************************************************)
(* AllSuccessors Tests                                                           *)
(******************************************************************************)
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]
       IN AssertEq(AllSuccessors(G, {1, 2}), {2, 3})

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]
       IN AssertEq(AllSuccessors(G, {2}), {})

(******************************************************************************)
(* Predecessors Tests                                                         *)
(******************************************************************************)
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
       IN AssertEq(Predecessors(G, 1), {2, 3})

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
       IN AssertEq(Predecessors(G, 2), {})

(******************************************************************************)
(* AllPredecessors Tests                                                         *)
(******************************************************************************)
ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
       IN AssertEq(AllPredecessors(G, {1, 2}), {2, 3})

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
       IN AssertEq(AllPredecessors(G, {2}), {})

(******************************************************************************)
(* Ancestors Tests                                                         *)
(******************************************************************************)
ASSUME LET G == [node |-> {1}, edge |-> {}]
       IN AssertEq(Ancestors(G, 1), {})

ASSUME LET G == [node |-> {1, 2, 3, 4}, edge |-> {<<4, 2>>, <<2, 1>>, <<3, 1>>}]
       IN AssertEq(Ancestors(G, 1), {2, 3, 4})

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]
       IN AssertEq(Ancestors(G, 1), {1, 2, 3})

ASSUME AssertEq(Ancestors([node |-> {1, 2, 3, 4},
                           edge |-> {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>}], 4), {1, 2, 3})


(******************************************************************************)
(* Descendants Tests                                                         *)
(******************************************************************************)
ASSUME LET G == [node |-> {1}, edge |-> {}]
       IN AssertEq(Descendants(G, 1), {})

ASSUME LET G == [node |-> {1, 2, 3, 4}, edge |-> {<<4, 2>>, <<2, 1>>, <<3, 1>>}]
       IN AssertEq(Descendants(G, 4), {1, 2})

ASSUME LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]
       IN AssertEq(Descendants(G, 1), {1, 2, 3})

ASSUME AssertEq(Descendants([node |-> {1, 2, 3, 4},
                             edge |-> {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>}], 1), {2, 3, 4})

(******************************************************************************)
(* Roots Tests                                                                *)
(******************************************************************************)
ASSUME AssertEq(Roots([node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]), {2, 3})

ASSUME AssertEq(Roots([node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]), {1})

ASSUME AssertEq(Roots([node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}]), {})

(******************************************************************************)
(* Leaves Tests                                                               *)
(******************************************************************************)
ASSUME AssertEq(Leaves([node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]), {1})

ASSUME AssertEq(Leaves([node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>}]), {2, 3})

ASSUME AssertEq(Leaves([node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}]), {})
=====================================================================
\* Modification History
\* Last modified Sun Mar 06 18:15:49 CET 2022 by Stephan Merz
\* Last modified Tue Dec 21 15:55:45 PST 2021 by Markus Kuppe
\* Created Mon Dec 20 20:55:45 PST 2021 by Markus Kuppe