------------------------- MODULE GraphVizTests -------------------------
EXTENDS GraphViz, Sequences, Naturals, TLC

ASSUME LET T == INSTANCE TLC IN T!PrintT("GraphViz")

ASSUME LET G ==  [node |-> {1,2,3}, 
                  edge |-> {<<1,2,1>>, <<2,3,2>>, <<2,1,3>>}]
       IN DotDiGraph(G, LAMBDA v : v, LAMBDA e: e[3] ) = "digraph MyGraph {-5002151522364771816[label=1];-2714544764469681861[label=2];-427540549684285478[label=3];-5002151522364771816->-2714544764469681861[label=1];-2714544764469681861->-5002151522364771816[label=3];-2714544764469681861->-427540549684285478[label=2];}"

=============================================================================
