------------------------------ MODULE GraphTheorems --------------------------
EXTENDS Graphs, Sequences

(****************************************************************************)
(* Lemmas about transposed graphs.                                          *)
(****************************************************************************)
THEOREM TransposeIsDirectedGraph ==
    ASSUME NEW G, IsDirectedGraph(G) 
    PROVE  IsDirectedGraph(Transpose(G))

\* Note that the reverse implication does not hold in general.
\* Consider G = [node |-> {1}, edge |-> {<<1,1,1>>}, root |-> {1}]
\* Then Transpose(G) = [node |-> {1}, edge |-> {<<1,1>>}],
\* which is a directed graph whereas G is not.

THEOREM TransposeTranspose == 
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  Transpose(Transpose(G)) = G 

THEOREM PathTranspose ==
    ASSUME NEW G, NEW p \in Path(G)
    PROVE  Reverse(p) \in Path(Transpose(G))

THEOREM TransposePath ==
    ASSUME NEW G, IsDirectedGraph(G), NEW p \in Path(Transpose(G))
    PROVE  Reverse(p) \in Path(G)

THEOREM SimplePathTranspose ==
    ASSUME NEW G, NEW p \in SimplePath(G)
    PROVE  Reverse(p) \in SimplePath(Transpose(G))

THEOREM TransposeSimplePath ==
    ASSUME NEW G, IsDirectedGraph(G), NEW p \in SimplePath(Transpose(G))
    PROVE  Reverse(p) \in SimplePath(G)

THEOREM AreConnectedInTranspose ==
    ASSUME NEW G, NEW m, NEW n, AreConnectedIn(m, n, G)
    PROVE  AreConnectedIn(n, m, Transpose(G))

THEOREM TransposeAreConnectedIn ==
    ASSUME NEW G, NEW m, NEW n, IsDirectedGraph(G), 
           AreConnectedIn(m, n, Transpose(G))
    PROVE  AreConnectedIn(n, m, G)

THEOREM IsStronglyConnectedTranspose ==
    ASSUME NEW G, IsStronglyConnected(G)
    PROVE  IsStronglyConnected(Transpose(G))

THEOREM TransposeIsStronglyConnected ==
    ASSUME NEW G, IsDirectedGraph(G), IsStronglyConnected(Transpose(G))
    PROVE  IsStronglyConnected(G)

(****************************************************************************)
(* The "concatenation" of two paths that share an endpoint is a path.       *)
(****************************************************************************)
THEOREM PathConcatenation ==
    ASSUME NEW G, NEW p \in Path(G), NEW q \in Path(G),
           p[Len(p)] = q[1] 
    PROVE  p \o Tail(q) \in Path(G)

(****************************************************************************)
(* Any non-empty subsequence of a path is a path.                           *)
(****************************************************************************)
THEOREM SubPath ==
    ASSUME NEW G, NEW p \in Path(G),
           NEW i \in 1 .. Len(p), NEW j \in i .. Len(p)
    PROVE  SubSeq(p, i, j) \in Path(G)

(****************************************************************************)
(* Two nodes are connected by a path if and only if they are connected by   *)
(* a simple path.                                                           *)
(****************************************************************************)
THEOREM ExistsPathIffExistsSimplePath ==
  ASSUME NEW G, NEW m \in G.node, NEW n \in G.node
  PROVE  (\E p \in Path(G) : p[1] = m /\ p[Len(p)] = n)
         <=> (\E p \in SimplePath(G) : p[1] = m /\ p[Len(p)] = n)

(****************************************************************************)
(* Connectedness is a pre-order.                                            *)
(****************************************************************************)
THEOREM ConnectedReflexive ==
    ASSUME NEW G, NEW a \in G.node
    PROVE  AreConnectedIn(a, a, G)

THEOREM ConnectedTransitive ==
    ASSUME NEW G, NEW a \in G.node, NEW b \in G.node, NEW c \in G.node,
           AreConnectedIn(a, b, G), AreConnectedIn(b, c, G)
    PROVE  AreConnectedIn(a, c, G)

(****************************************************************************)
(* A tree does not contain a cycle. One way to express this is that no      *)
(* non-empty set of nodes is closed under successors.                       *)
(****************************************************************************)
THEOREM TreeAcyclic ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), NEW S \in SUBSET G.node, S # {}
    PROVE  \E q \in S : \A e \in G.edge : e[1] = q => e[2] \notin S 

(****************************************************************************)
(* In particular, no node is its own successor in a tree, and all paths in  *)
(* a tree are simple paths.                                                 *)
(****************************************************************************)
THEOREM TreeIrreflexive ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), NEW n \in G.node
    PROVE  <<n,n>> \notin G.edge

THEOREM TreeSimplePath ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), NEW p \in Path(G)
    PROVE  p \in SimplePath(G)

(****************************************************************************)
(* Connectedness is antisymmetric (and thus a partial order) in trees.      *)
(****************************************************************************)
THEOREM TreeConnectedAntisymmetric ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), 
           NEW a \in G.node, NEW b \in G.node,
           AreConnectedIn(a, b, G), AreConnectedIn(b, a, G)
    PROVE  a = b 

(****************************************************************************)
(* A graph consisting of only the root and no edges is a tree.              *)
(****************************************************************************)
THEOREM SingletonIsTreeWithRoot ==
    ASSUME NEW r
    PROVE IsTreeWithRoot([node |-> {r}, edge |-> {}],r)

(****************************************************************************)
(* A tree can be extended by attaching a disjoint tree to a node.           *)
(****************************************************************************)
THEOREM AttachTree ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), NEW n \in G.node,
           NEW H, NEW s, IsTreeWithRoot(H,s), G.node \cap H.node = {} 
    PROVE  IsTreeWithRoot([node |-> G.node \cup H.node,
                           edge |-> G.edge \cup H.edge \cup {<<s,n>>}], r)

(****************************************************************************)
(* In particular, a tree can be extended by a new node that becomes a leaf. *)
(****************************************************************************)
THEOREM AddLeafToTree == 
    ASSUME NEW G, NEW r, NEW leaf, NEW parent,
           IsTreeWithRoot(G,r), leaf \notin G.node, parent \in G.node
    PROVE  IsTreeWithRoot([node |-> G.node \cup {leaf}, 
                           edge |-> G.edge \cup {<<leaf, parent>>}], r)

(****************************************************************************)
(* Removing a subtree from a tree maintains the tree property, provided it  *)
(* is not the entire tree (trees must be non-empty.)                        *)
(****************************************************************************)
THEOREM RemoveSubtree == 
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r),
           NEW nd \in G.node \ {r}
    PROVE  LET S == { n \in G.node : AreConnectedIn(n, nd, G) }
               T == G.node \ S 
               E == G.edge \cap (T \X T)
           IN  IsTreeWithRoot([node |-> T, edge |-> E], r)

(****************************************************************************)
(* In particular, removing a leaf node that is not the root from a tree     *)
(* results in a tree.                                                       *)
(****************************************************************************)
THEOREM RemoveLeafFromTree == 
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r),
           NEW leaf \in G.node, Predecessors(G, leaf) = {},
           NEW parent \in G.node, <<leaf, parent>> \in G.edge
    PROVE  IsTreeWithRoot([node |-> G.node \ {leaf}, 
                           edge |-> G.edge \ {<<leaf, parent>>}], r)

(****************************************************************************)
(* The operator IsTreeWithRoot is set up so that edges point towards the    *)
(* root of the tree. Sometimes it is more natural to consider trees with    *)
(* edges pointing towards the leaves. Such a graph G can be characterized   *)
(* by the predicate IsTreeWithRoot(Transpose(G), r).                        *)
(* We prove lemmas analogous to the above ones about transposed trees.      *)
(****************************************************************************)
THEOREM SingletonIsTransposedTreeWithRoot ==
    ASSUME NEW r
    PROVE IsTreeWithRoot(Transpose([node |-> {r}, edge |-> {}]), r)

THEOREM AttachTransposedTree ==
    ASSUME NEW G, NEW r, IsDirectedGraph(G), IsTreeWithRoot(Transpose(G), r),
           NEW H, NEW s, IsDirectedGraph(H), IsTreeWithRoot(Transpose(H), s),
           G.node \cap H.node = {}, NEW n \in G.node
    PROVE  IsTreeWithRoot(Transpose([node |-> G.node \cup H.node,
                                     edge |-> G.edge \cup H.edge \cup {<<n,s>>}]), r)

THEOREM AddLeafToTransposedTree == 
    ASSUME NEW G, NEW r, NEW leaf, NEW parent,
           IsDirectedGraph(G), IsTreeWithRoot(Transpose(G),r),
           leaf \notin G.node, parent \in G.node
    PROVE  IsTreeWithRoot(Transpose([node |-> G.node \cup {leaf}, 
                                     edge |-> G.edge \cup {<<parent, leaf>>}]), r)

THEOREM RemoveTransposedSubtree ==
    ASSUME NEW G, NEW r, IsDirectedGraph(G), IsTreeWithRoot(Transpose(G), r),
           NEW nd \in G.node \ {r}
    PROVE  LET S == {n \in G.node : AreConnectedIn(nd, n, G)}
               T == G.node \ S 
               E == G.edge \cap (T \X T)
           IN  IsTreeWithRoot(Transpose([node |-> T, edge |-> E]), r)

THEOREM RemoveLeafFromTransposedTree ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW r, IsTreeWithRoot(Transpose(G),r),
           NEW leaf \in G.node,
           Successors(G, leaf) = {},
           NEW parent \in G.node, <<parent, leaf>> \in G.edge
    PROVE  IsTreeWithRoot(Transpose([node |-> G.node \ {leaf}, 
                                     edge |-> G.edge \ {<<parent, leaf>>}]), r)

==============================================================================
