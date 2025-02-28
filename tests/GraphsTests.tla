------------------------- MODULE GraphsTests -------------------------
EXTENDS Graphs, TLCExt
ASSUME LET T == INSTANCE TLC IN T!PrintT("GraphsTests")
ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {}]), {})
ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {1,2,3}]), {<<1>>, <<2>>, <<3>>})
ASSUME AssertEq(SimplePath([edge|-> {<<1,2>>, <<2,3>>}, node |-> {1,2,3}]), 
            { <<1>>, <<2>>, <<3>>, <<1,2>>, <<2,3>>, <<1,2,3>> } )
Graphs(nodes) ==
    [node : {nodes}, edge : SUBSET (nodes \X nodes)]
ASSUME \A g \in Graphs({"A", "B", "C"}):
    \A u,v \in g.node :
        AreConnectedIn(u, v, g) \in BOOLEAN 
ASSUME LET G ==  [node |-> {1,2,3,4,5,6}, 
                  edge |-> {<<1,2>>, <<2,3>>, <<2,4>>, <<3,2>>, <<3,4>>, <<3,5>>, 
                            <<4,2>>, <<5,6>>, <<6,5>>}]
       IN  \A m,n \in G.node : AreConnectedIn(m,n,G) <=> ConnectionsIn(G)[m,n]

\* Tests for IsTreeWithRoot
ASSUME LET SingleNodeGraph == [node |-> {"r"}, edge |-> {}]
       IN IsTreeWithRoot(SingleNodeGraph, "r")

ASSUME LET ValidTree == [node |-> {"r", "a", "b", "c"},
                        edge |-> {<<"r", "a">>, <<"a", "b">>, <<"a", "c">>}]
       IN IsTreeWithRoot(ValidTree, "r")

ASSUME LET CyclicGraph == [node |-> {"r", "a", "b"},
                          edge |-> {<<"r", "a">>, <<"a", "b">>, <<"b", "r">>}]
       IN ~IsTreeWithRoot(CyclicGraph, "r")

ASSUME LET MultiParentGraph == [node |-> {"r", "a", "b"},
                               edge |-> {<<"r", "a">>, <<"b", "a">>}]
       IN ~IsTreeWithRoot(MultiParentGraph, "r")

ASSUME LET DisconnectedGraph == [node |-> {"r", "a", "b"},
                                edge |-> {<<"r", "a">>}]
       IN ~IsTreeWithRoot(DisconnectedGraph, "r")

=====================================================================
\* Modification History
\* Last modified Thu Nov 11 10:45:50 CET 2024 by Younes Akhouayri
\* Last modified Sun Mar 06 18:15:49 CET 2022 by Stephan Merz
\* Last modified Tue Dec 21 15:55:45 PST 2021 by Markus Kuppe
\* Created Mon Dec 20 20:55:45 PST 2021 by Markus Kuppe
