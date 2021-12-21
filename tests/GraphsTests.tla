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
=====================================================================
\* Modification History
\* Last modified Tue Dec 21 15:55:45 PST 2021 by Markus Kuppe
\* Created Mon Dec 20 20:55:45 PST 2021 by Markus Kuppe