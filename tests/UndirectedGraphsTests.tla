------------------------- MODULE UndirectedGraphsTests -----------------------
EXTENDS UndirectedGraphs, SequencesExt, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("UndirectedGraphsTests")

(******************************************************************************)
(* Pure TLA+ reference definitions that can be evaluated by TLC and that      *)
(* as oracles against which the module overrides (SimplePath, AreConnectedIn, *)
(* ConnectedComponents) are checked below.                                    *)
(******************************************************************************)

LOCAL SimplePathPure(G) ==
    {p \in SeqOf(G.node, Cardinality(G.node)) :
             /\ p # << >>
             /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
             /\ \A i \in 1..(Len(p)-1) : {p[i], p[i+1]} \in G.edge}

LOCAL ConnectedComponentsPure(G) ==
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

LOCAL AreConnectedInPure(m, n, G) ==
   \E comp \in ConnectedComponentsPure(G) : m \in comp /\ n \in comp

\* Undirected graphs with one, two or three nodes.
LOCAL SmallGraphs ==
    UndirectedGraphs({}) \cup 
    UndirectedGraphs({1}) \cup 
    UndirectedGraphs({1,2}) \cup 
    UndirectedGraphs({1,2,3})

\* An undirected graph whose edge set is built via a set image that yields
\* the same edge multiple times: make sure the Java overrides work as expected.
LOCAL DupEdgeGraph ==
    [node |-> {1,2,3},
     edge |-> {{2,3}} \cup { {1,2} : i \in {"a", "b", "c"}}]

\* An undirected graph containing "edges" that are sets containing
\* not exactly one or two elements or elements that are not nodes.
\* Such "edges" will be ignored by the Java overrides.
LOCAL MalformedGraph ==
    [node |-> {1,2,3},
     edge |-> { {}, {1}, {1,2}, {3,2,1}, {5,6}}]

------------------------------------------------------------------------------
(******************************************************************************)
(* SimplePath tests.                                                          *)
(******************************************************************************)

ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {}]), {})
ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {1,2,3}]), {<<1>>, <<2>>, <<3>>})
ASSUME AssertEq(SimplePath([edge|-> {{1,2}}, node |-> {1,2,3}]), 
            { <<1>>, <<2>>, <<3>>, <<1,2>>, <<2,1>>} )
                
ASSUME AssertEq(SimplePath(DupEdgeGraph), 
                {<<1>>, <<2>>, <<3>>, <<1,2>>, <<2,1>>, <<2,3>>, <<3,2>>, <<1,2,3>>, <<3,2,1>>})
ASSUME AssertEq(SimplePath(MalformedGraph),
                {<<1>>, <<2>>, <<3>>, <<1,2>>, <<2,1>>})
ASSUME \A g \in SmallGraphs : AssertEq(SimplePath(g), SimplePathPure(g))

(******************************************************************************)
(* AreConnectedIn tests.                                                      *)
(******************************************************************************)
ASSUME LET G == [edge|-> {{1,2}}, node |-> {1,2,3}]
       IN  /\ AreConnectedIn(1, 2, G)
           /\ ~ AreConnectedIn(1, 3, G)

ASSUME \A m,n \in DupEdgeGraph.node : AreConnectedIn(m, n, DupEdgeGraph)

ASSUME /\ AreConnectedIn(1, 2, MalformedGraph)
       /\ ~ AreConnectedIn(3, 2, MalformedGraph)

ASSUME \A g \in SmallGraphs : \A m,n \in g.node :
          /\ AssertEq(AreConnectedIn(m, n, g), AreConnectedInPure(m, n, g))
          /\ AssertEq(AreConnectedIn(m, n, g), AreConnectedIn(n, m, g))

(******************************************************************************)
(* ConnectedComponents tests.                                                 *)
(******************************************************************************)
ASSUME AssertEq(ConnectedComponents([edge|-> {}, node |-> {}]), {})

ASSUME LET G == [edge|-> {{1,2}}, node |-> {1,2,3}]
       IN  AssertEq(ConnectedComponents(G), {{1,2}, {3}})

ASSUME LET G == [node |-> {1,2,3,4,5},
                 edge |-> {{1,3}, {1,4}, {2,3}, {2,4}, {3,5}, {4,5}}]
       IN  /\ AssertEq(ConnectedComponents(G), {{1,2,3,4,5}})
           /\ IsStronglyConnected(G)

ASSUME /\ AssertEq(ConnectedComponents(DupEdgeGraph), { {1,2,3} })
       /\ IsStronglyConnected(DupEdgeGraph)

ASSUME /\ AssertEq(ConnectedComponents(MalformedGraph), { {1,2}, {3} })
       /\ ~ IsStronglyConnected(MalformedGraph)

ASSUME \A g \in SmallGraphs : 
    AssertEq(ConnectedComponents(g), ConnectedComponentsPure(g))

=====================================================================
