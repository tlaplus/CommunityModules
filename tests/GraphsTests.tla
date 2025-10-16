------------------------- MODULE GraphsTests -------------------------
EXTENDS Graphs, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("GraphsTests")

ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {}]), {})
ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {1,2,3}]), {<<1>>, <<2>>, <<3>>})
ASSUME AssertEq(SimplePath([edge|-> {<<1,2>>, <<2,3>>}, node |-> {1,2,3}]), 
            { <<1>>, <<2>>, <<3>>, <<1,2>>, <<2,3>>, <<1,2,3>> } )

ASSUME \A g \in Graphs({"A", "B", "C"}):
    \A u,v \in g.node :
        AreConnectedIn(u, v, g) \in BOOLEAN 

ASSUME LET G ==  [node |-> {1,2,3,4,5,6}, 
                  edge |-> {<<1,2>>, <<2,3>>, <<2,4>>, <<3,2>>, <<3,4>>, <<3,5>>, 
                            <<4,2>>, <<5,6>>, <<6,5>>}]
       IN  \A m,n \in G.node : AreConnectedIn(m,n,G) <=> ConnectionsIn(G)[m,n]

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