------------------------- MODULE GraphsTests -------------------------
EXTENDS UndirectedGraphs, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("UndirectedGraphsTests")

ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {}]), {})
ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {1,2,3}]), {<<1>>, <<2>>, <<3>>})
ASSUME AssertEq(SimplePath([edge|-> {{1,2}}, node |-> {1,2,3}]), 
            { <<1>>, <<2>>, <<3>>, <<1,2>>, <<2,1>>} )

ASSUME AssertEq(ConnectedComponents([edge|-> {}, node |-> {}]), {})
ASSUME LET G == [edge|-> {{1,2}}, node |-> {1,2,3}]
       IN  /\ AssertEq(ConnectedComponents(G), {{1,2}, {3}})
           /\ AreConnectedIn(1, 2, G)
           /\ ~ AreConnectedIn(1, 3, G)

AssertEq(ConnectedComponents([edge|-> {{1,2}}, node |-> {1,2,3}]), 
                {{1,2}, {3}})
ASSUME LET G == [node |-> {1,2,3,4,5},
                 edge |-> {{1,3}, {1,4}, {2,3}, {2,4}, {3,5}, {4,5}}]
       IN  /\ AssertEq(ConnectedComponents(G), {{1,2,3,4,5}})
           /\ IsStronglyConnected(G)

=====================================================================
