------------------------- MODULE GraphsTests -------------------------
EXTENDS Graphs, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("GraphsTests")

ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {}]), {})
ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {1,2,3}]), {<<1>>, <<2>>, <<3>>})
ASSUME AssertEq(SimplePath([edge|-> {<<1,2>>, <<2,3>>}, node |-> {1,2,3}]), 
            { <<1>>, <<2>>, <<3>>, <<1,2>>, <<2,3>>, <<1,2,3>> } )

ASSUME LET G ==  [node |-> {1,2,3,4,5,6}, 
                  edge |-> {<<1,2>>, <<2,3>>, <<2,4>>, <<3,2>>, <<3,4>>, <<3,5>>, 
                            <<4,2>>, <<5,6>>, <<6,5>>}]
       IN  \A m,n \in G.node : AreConnectedIn(m,n,G) <=> ConnectionsIn(G)[m,n]

Graphs(nodes) ==
    [node : {nodes}, edge : SUBSET (nodes \X nodes)]

ASSUME \A g \in Graphs({"A", "B", "C"}):
    \A u,v \in g.node :
        AreConnectedIn(u, v, g) \in BOOLEAN 
=====================================================================
\* Modification History
\* Last modified Sun Mar 06 18:15:49 CET 2022 by merz
\* Last modified Tue Dec 21 15:55:45 PST 2021 by Markus Kuppe
\* Created Mon Dec 20 20:55:45 PST 2021 by Markus Kuppe