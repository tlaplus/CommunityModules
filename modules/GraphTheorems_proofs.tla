---------------------- MODULE GraphTheorems_proofs --------------------------
EXTENDS Graphs, Integers, FunctionTheorems, FiniteSetTheorems, 
        SequencesExtTheorems,
        FiniteSetsExt, FiniteSetsExtTheorems, TLAPS

(****************************************************************************)
(* Lemmas about transposed graphs.                                          *)
(****************************************************************************)
THEOREM TransposeIsDirectedGraph ==
    ASSUME NEW G, IsDirectedGraph(G) 
    PROVE  IsDirectedGraph(Transpose(G))
<1>. DEFINE N == G.node  
            E == G.edge
<1>1. /\ G = [node |-> N, edge |-> E]
      /\ E \subseteq N \X N 
  BY DEF IsDirectedGraph
<1>. HIDE DEF N, E 
<1>. QED  BY <1>1 DEF IsDirectedGraph, Transpose 

THEOREM TransposeTranspose == 
    ASSUME NEW G, IsDirectedGraph(G)
    PROVE  Transpose(Transpose(G)) = G 
<1>. DEFINE N == G.node  
            E == G.edge
            TE == { <<e[2], e[1]>> : e \in E }
            TTE == { <<e[2], e[1]>> : e \in TE }
<1>1. /\ G = [node |-> N, edge |-> E]
      /\ E \subseteq N \X N 
      /\ TE \subseteq N \X N 
  BY DEF IsDirectedGraph
<1>. HIDE DEF N, E 
<1>2. Transpose(G) = [node |-> N, edge |-> TE]
  BY <1>1 DEF Transpose 
<1>3. TTE = E 
  BY <1>1
<1>4. Transpose(Transpose(G)) = [node |-> N, edge |-> TTE]
  BY <1>2 DEF Transpose 
<1>. HIDE DEF TTE
<1>. QED  BY <1>1, <1>3, <1>4

THEOREM PathTranspose ==
    ASSUME NEW G, NEW p \in Path(G)
    PROVE  Reverse(p) \in Path(Transpose(G))
BY DEF Path, Reverse, Transpose 

THEOREM TransposePath ==
    ASSUME NEW G, IsDirectedGraph(G), NEW p \in Path(Transpose(G))
    PROVE  Reverse(p) \in Path(G)
<1>. DEFINE N == G.node 
            E == G.edge 
            TE == { <<e[2], e[1]>> : e \in E }
<1>1. /\ G = [node |-> N, edge |-> E]
      /\ E \subseteq N \X N
  BY DEF IsDirectedGraph 
<1>2. Transpose(G) = [node |-> N, edge |-> TE]
  BY DEF Transpose 
<1>. HIDE DEF N, E
<1>3. /\ p \in Seq(N) \ { <<>> }
      /\ \A i \in 1 .. Len(p)-1 : <<p[i], p[i+1]>> \in TE
  BY <1>2 DEF Path
<1>. QED  BY <1>1, <1>3 DEF Reverse, Path 

THEOREM SimplePathTranspose ==
    ASSUME NEW G, NEW p \in SimplePath(G)
    PROVE  Reverse(p) \in SimplePath(Transpose(G))
<1>1. /\ Reverse(p) \in Path(Transpose(G))
      /\ \A i,j \in 1 .. Len(p) : p[i] = p[j] => i = j
  BY PathTranspose DEF SimplePath 
<1>2. p \in Seq(G.node)
  BY DEF SimplePath, Path 
<1>. QED  BY <1>1, <1>2 DEF Reverse, SimplePath 

THEOREM TransposeSimplePath ==
    ASSUME NEW G, IsDirectedGraph(G), NEW p \in SimplePath(Transpose(G))
    PROVE  Reverse(p) \in SimplePath(G)
<1>1. /\ Reverse(p) \in Path(G)
      /\ \A i,j \in 1 .. Len(p) : p[i] = p[j] => i = j
  BY TransposePath DEF SimplePath 
<1>2. p \in Seq(G.node)
  BY DEF SimplePath, Path, Transpose 
<1>. QED  BY <1>1, <1>2 DEF Reverse, SimplePath 

THEOREM AreConnectedInTranspose ==
    ASSUME NEW G, NEW m, NEW n, AreConnectedIn(m, n, G)
    PROVE  AreConnectedIn(n, m, Transpose(G))
<1>1. PICK p \in Path(G) : p[1] = m /\ p[Len(p)] = n 
  BY DEF AreConnectedIn 
<1>. p \in Seq(G.node) \ { << >> }
  BY DEF Path 
<1>2. Reverse(p) \in Path(Transpose(G))
  BY PathTranspose
<1>3. Reverse(p)[1] = n /\ Reverse(p)[Len(Reverse(p))] = m 
  BY <1>1 DEF Reverse 
<1>. QED  BY <1>2, <1>3 DEF AreConnectedIn 

THEOREM TransposeAreConnectedIn ==
    ASSUME NEW G, NEW m, NEW n, IsDirectedGraph(G), AreConnectedIn(m, n, Transpose(G))
    PROVE  AreConnectedIn(n, m, G)
<1>1. PICK p \in Path(Transpose(G)) : p[1] = m /\ p[Len(p)] = n 
  BY DEF AreConnectedIn 
<1>. p \in Seq(G.node) \ { << >> }
  BY DEF Path, Transpose 
<1>2. Reverse(p) \in Path(G)
  BY TransposePath
<1>3. Reverse(p)[1] = n /\ Reverse(p)[Len(Reverse(p))] = m 
  BY <1>1 DEF Reverse 
<1>. QED  BY <1>2, <1>3 DEF AreConnectedIn 

THEOREM IsStronglyConnectedTranspose ==
    ASSUME NEW G, IsStronglyConnected(G)
    PROVE  IsStronglyConnected(Transpose(G))
<1>. Transpose(G).node = G.node
  BY DEF Transpose 
<1>. QED  BY AreConnectedInTranspose DEF IsStronglyConnected 

THEOREM TransposeIsStronglyConnected ==
    ASSUME NEW G, IsDirectedGraph(G), IsStronglyConnected(Transpose(G))
    PROVE  IsStronglyConnected(G)
<1>. Transpose(G).node = G.node
  BY DEF Transpose 
<1>. QED  BY TransposeAreConnectedIn DEF IsStronglyConnected 

(****************************************************************************)
(* The "concatenation" of two paths that share an endpoint is a path.       *)
(****************************************************************************)
THEOREM PathConcatenation ==
    ASSUME NEW G, NEW p \in Path(G), NEW q \in Path(G),
           p[Len(p)] = q[1] 
    PROVE  p \o Tail(q) \in Path(G)
<1>. DEFINE pq == p \o Tail(q)
<1>. p \in Seq(G.node) \ { <<>> } /\ q \in Seq(G.node) \ { <<>> }
  BY DEF Path 
<1>2. ASSUME NEW i \in 1 .. Len(pq)-1  PROVE <<pq[i], pq[i+1]>> \in G.edge
  <2>1. CASE i \in 1 .. Len(p)-1
    BY <2>1 DEF Path 
  <2>2. CASE i \in Len(p) .. Len(pq)-1
    BY <2>2, i-Len(p)+1 \in 1 .. Len(q)-1 DEF Path 
  <2>. QED  BY <2>1, <2>2
<1>. QED  BY <1>2 DEF Path 

(****************************************************************************)
(* Any non-empty subsequence of a path is a path.                           *)
(****************************************************************************)
THEOREM SubPath ==
    ASSUME NEW G, NEW p \in Path(G),
           NEW i \in 1 .. Len(p), NEW j \in i .. Len(p)
    PROVE  SubSeq(p, i, j) \in Path(G)
<1>. DEFINE s == SubSeq(p, i, j)
<1>. p \in Seq(G.node)
  BY DEF Path 
<1>1. /\ s \in Seq(G.node) \ { <<>> }
      /\ Len(s) = j-i+1
  OBVIOUS 
<1>2. ASSUME NEW k \in 1 .. (j-i) PROVE <<s[k], s[k+1]>> \in G.edge
  BY i+k-1 \in 1 .. Len(p)-1 DEF Path 
<1>. QED  BY <1>1, <1>2 DEF Path 

(****************************************************************************)
(* Two nodes are connected by a path if and only if they are connected by   *)
(* a simple path.                                                           *)
(****************************************************************************)
THEOREM ExistsPathIffExistsSimplePath ==
  ASSUME NEW G, NEW m \in G.node, NEW n \in G.node
  PROVE  (\E p \in Path(G) : p[1] = m /\ p[Len(p)] = n)
         <=> (\E p \in SimplePath(G) : p[1] = m /\ p[Len(p)] = n)
<1>1. SUFFICES ASSUME NEW p \in Path(G), p[1] = m, p[Len(p)] = n 
               PROVE  \E q \in SimplePath(G) : q[1] = m /\ q[Len(q)] = n 
  BY DEF SimplePath
<1>. DEFINE Repeats(pp) == {i \in 1 .. Len(pp) : \E j \in 1 .. Len(pp) : j > i /\ pp[i] = pp[j]}
            CR(pp) == Cardinality(Repeats(pp))
            P(pp,k) == pp[1] = m /\ pp[Len(pp)] = n /\ CR(pp) = k 
                       => \E q \in SimplePath(G) : q[1] = m /\ q[Len(q)] = n 
<1>2. ASSUME NEW pp \in Path(G)
      PROVE  IsFiniteSet(Repeats(pp))
  BY FS_Subset, FS_Interval DEF Path
<1>3. \E k \in Nat : CR(p) = k
  BY <1>2, FS_CardinalityType, Zenon
<1>4. \A k \in Nat : \A pp \in Path(G) : P(pp,k)
  <2>. SUFFICES \A k \in Nat : (\A l \in 0 .. k-1 : \A pp \in Path(G) : P(pp,l))
                               => \A pp \in Path(G) : P(pp,k)
    <3>. HIDE DEF P 
    <3>. QED  BY GeneralNatInduction, IsaM("iprover")
  <2>1. SUFFICES ASSUME NEW k \in Nat,
                        \A l \in 0 .. k-1 : \A pp \in Path(G) : P(pp,l),
                        NEW pp \in Path(G), pp[1] = m, pp[Len(pp)] = n, CR(pp) = k
                 PROVE  \E q \in SimplePath(G) : q[1] = m /\ q[Len(q)] = n 
    BY Zenon
  <2>. pp \in Seq(G.node)
    BY DEF Path
  <2>2. CASE k = 0
    <3>. Repeats(pp) = {}
      BY <1>2, <2>1, <2>2, FS_EmptySet, Zenon
    <3>. QED  BY <2>1 DEF SimplePath
  <2>3. CASE k # 0
    <3>1. PICK i \in 1 .. Len(pp) : \E j \in 1 .. Len(pp) : j > i /\ pp[i] = pp[j]
      BY <1>2, <2>1, <2>3, FS_EmptySet
    <3>2. PICK j \in 1 .. Len(pp) : /\ j > i /\ pp[i] = pp[j] 
                                    /\ ~(\E jj \in 1 .. Len(pp) : jj > j /\ pp[i] = pp[jj])
      <4>. DEFINE J == {jj \in 1 .. Len(pp) : jj > i /\ pp[i] = pp[jj]}
      <4>1. /\ J \in SUBSET Int 
            /\ J # {}
            /\ Len(pp) \in Int 
            /\ \A jj \in J : Len(pp) >= jj
        BY <3>1
      <4>2. /\ Max(J) \in J
            /\ \A jj \in J : Max(J) >= jj
        BY <4>1, MaxIntBounded
      <4>. QED  BY <4>2
    <3>. DEFINE pref == SubSeq(pp, 1, i)
                suff == SubSeq(pp, j+1, Len(pp))
                qq == pref \o suff
    <3>3. qq \in Path(G)
      <4>1. qq \in Seq(G.node)
        OBVIOUS
      <4>2. qq # << >> 
        BY <3>2 DEF Path
      <4>3. ASSUME NEW ii \in 1 .. Len(qq)-1
            PROVE  <<qq[ii], qq[ii+1]>> \in G.edge
        <5>1. CASE ii \in 1 .. i-1
          BY <5>1 DEF Path 
        <5>2. CASE ii = i 
          BY <3>2, <5>2 DEF Path
        <5>3. CASE ii > i
          <6>1. /\ qq[ii] = pp[j-i+ii]
                /\ qq[ii+1] = pp[j-i+ii+1]
            BY <3>2, <5>3
          <6>. QED  BY <3>2, <6>1 DEF Path 
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>. QED  BY <4>1, <4>2, <4>3 DEF Path 
    <3>4. CR(qq) \in 0 .. k-1
      <4>. DEFINE inj == [ii \in Repeats(qq) |-> IF ii <= i THEN ii ELSE j-i+ii]
      <4>1. ASSUME NEW ii \in Repeats(qq)
            PROVE  inj[ii] \in Repeats(pp)
        BY <3>2
      <4>2. inj \in [Repeats(qq) -> Repeats(pp)]
        BY <4>1, Zenon
      <4>3. \A ii,jj \in Repeats(qq) : inj[ii] = inj[jj] => ii = jj
        BY <3>2
      <4>4. inj \in Injection(Repeats(qq), Repeats(pp))
        BY <4>2, <4>3, Fun_IsInj, Zenon
      <4>5. CR(qq) <= CR(pp)
        BY <1>2, <4>4, FS_Injection, Zenon
      <4>6. i \in Repeats(pp)
        BY <3>1
      <4>7. i \notin Repeats(qq)
        BY <3>2
      <4>8. inj \notin Surjection(Repeats(qq), Repeats(pp))
        BY <3>2, <4>6, <4>7, SMTT(10) DEF Surjection
      <4>9. /\ CR(qq) <= CR(pp)
            /\ CR(qq) # CR(pp)
        <5>. HIDE DEF Repeats, inj, qq
        <5>. QED  BY <1>2, <4>4, <4>8, FS_Injection, Zenon
      <4>. QED  BY <1>2, <2>1, <3>3, <4>9, FS_CardinalityType, Isa
    <3>5. qq[1] = m 
      BY <2>1 DEF Path
    <3>6. qq[Len(qq)] = n 
      BY <2>1, <3>2 DEF Path
    <3>. HIDE DEF CR, qq
    <3>. QED  BY <2>1, <3>3, <3>4, <3>5, <3>6
  <2>. HIDE DEF P
  <2>. QED  BY <2>2, <2>3, NatInduction, Isa
<1>. QED  BY <1>1, <1>3, <1>4, Zenon

(****************************************************************************)
(* Connectedness is a pre-order.                                            *)
(****************************************************************************)
THEOREM ConnectedReflexive ==
    ASSUME NEW G, NEW a \in G.node
    PROVE  AreConnectedIn(a, a, G)
BY <<a>> \in Seq(G.node) DEF AreConnectedIn, Path 

THEOREM ConnectedTransitive ==
    ASSUME NEW G, NEW a \in G.node, NEW b \in G.node, NEW c \in G.node,
           AreConnectedIn(a, b, G), AreConnectedIn(b, c, G)
    PROVE  AreConnectedIn(a, c, G)
<1>1. PICK p \in Path(G) : p[1] = a /\ p[Len(p)] = b 
  BY DEF AreConnectedIn 
<1>2. PICK q \in Path(G) : q[1] = b /\ q[Len(q)] = c
  BY DEF AreConnectedIn 
<1>. DEFINE pq == p \o Tail(q)
<1>3. pq \in Path(G)
  BY <1>1, <1>2, PathConcatenation
<1>4. pq[1] = a /\ pq[Len(pq)] = c
  BY <1>1, <1>2 DEF Path 
<1>. QED  BY <1>3, <1>4 DEF AreConnectedIn, Path 

(****************************************************************************)
(* A tree does not contain a cycle. One way to express this is that no      *)
(* non-empty set of nodes is closed under successors.                       *)
(****************************************************************************)
THEOREM TreeAcyclic ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), NEW S \in SUBSET G.node, S # {}
    PROVE  \E q \in S : \A e \in G.edge : e[1] = q => e[2] \notin S 
<1>. DEFINE RootPaths(n) == {p \in Path(G) : p[1] = n /\ p[Len(p)] = r}
            height(n) == Min({Len(p) : p \in RootPaths(n)})
<1>1. \A n \in G.node : RootPaths(n) # {}
  BY DEF IsTreeWithRoot, AreConnectedIn
<1>2. \A n \in G.node : /\ height(n) \in Nat
                        /\ \E p \in RootPaths(n) : Len(p) = height(n) 
                        /\ \A p \in RootPaths(n) : Len(p) >= height(n)
  <2>. TAKE n \in G.node
  <2>1. {Len(p) : p \in RootPaths(n)} \in (SUBSET Nat) \ {{}}
    BY <1>1 DEF Path 
  <2>2. /\ height(n) \in {Len(p) : p \in RootPaths(n)}
        /\ \A l \in {Len(p) : p \in RootPaths(n)} : height(n) <= l 
    BY <2>1, MinNat
  <2>. QED  BY <2>1, <2>2
<1>3. ASSUME NEW e \in G.edge
      PROVE  height(e[2]) < height(e[1])
  <2>1. e[1] \in G.node /\ e[2] \in G.node
    BY DEF IsTreeWithRoot, IsDirectedGraph
  <2>2. PICK p \in RootPaths(e[1]) : Len(p) = height(e[1])
    BY <1>2, <2>1
  <2>. p \in Seq(G.node) \ {<< >>}
    BY DEF Path 
  <2>3. p[1] = e[1] /\ p[Len(p)] = r 
    BY DEF Path 
  <2>4. e[1] # r 
    BY DEF IsTreeWithRoot 
  <2>5. Len(p) >= 2
    BY <2>3, <2>4
  <2>6. <<p[1], p[2]>> \in G.edge
    BY <2>5, 1 \in 1 .. Len(p)-1 DEF Path 
  <2>7. p[2] = e[2]
    BY <2>3, <2>6 DEF IsTreeWithRoot 
  <2>. DEFINE q == Tail(p)
  <2>8. q \in RootPaths(e[2])
    <3>1. q \in Seq(G.node) \ {<< >>}
      BY <2>5
    <3>2. ASSUME NEW i \in 1 .. Len(q)-1
          PROVE  <<q[i], q[i+1]>> \in G.edge
      BY i+1 \in 1 .. Len(p)-1 DEF Path
    <3>3. q[1] = e[2] /\ q[Len(q)] = r
      BY <2>5, <2>7
    <3>. QED  BY <3>1, <3>2, <3>3 DEF Path 
  <2>. HIDE DEF height
  <2>. QED  BY <1>2, <2>1, <2>2, <2>8
<1>4. PICK q \in S : \A n \in S : height(q) <= height(n)
  <2>. HIDE DEF height 
  <2>. DEFINE HS == {height(n) : n \in S}  mh == Min(HS)
  <2>1. HS \in (SUBSET Nat) \ {{}}
    BY <1>2
  <2>2. /\ mh \in HS
        /\ \A h \in HS : mh <= h
    BY <2>1, MinNat
  <2>. QED  BY <2>2
<1>. HIDE DEF RootPaths
<1>. QED  BY <1>2, <1>3, <1>4

(****************************************************************************)
(* In particular, no node is its own successor in a tree, and all paths in  *)
(* a tree are simple paths.                                                 *)
(****************************************************************************)
THEOREM TreeIrreflexive ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), NEW n \in G.node
    PROVE  <<n,n>> \notin G.edge
<1>1. PICK q \in {n} : \A e \in G.edge : e[1] = q => e[2] \notin {n}
  BY TreeAcyclic, Zenon
<1>. QED  BY <1>1

THEOREM TreeSimplePath ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), NEW p \in Path(G)
    PROVE  p \in SimplePath(G)
<1>. SUFFICES ASSUME NEW i \in 1 .. Len(p), NEW j \in 1 .. Len(p), i < j, p[i] = p[j]
              PROVE  FALSE 
  BY DEF SimplePath 
<1>. p \in Seq(G.node) \ { << >> }
  BY DEF Path 
<1>. DEFINE S == {p[k] : k \in i .. j}
<1>1. PICK k \in i..j : \A e \in G.edge : e[1] = p[k] => e[2] \notin S 
  BY TreeAcyclic, S \subseteq G.node, S # {}
<1>2. CASE k < j
  <2>1. /\ <<p[k], p[k+1]>> \in G.edge
        /\ p[k+1] \in S 
    BY <1>2 DEF Path 
  <2>. QED  BY <1>1, <2>1
<1>3. CASE k = j
  <2>1. /\ <<p[i], p[i+1]>> \in G.edge
        /\ p[i+1] \in S 
    BY DEF Path 
  <2>. QED  BY <1>1, <1>3, <2>1
<1>. QED  BY <1>2, <1>3

(****************************************************************************)
(* Connectedness is antisymmetric (and thus a partial order) in trees.      *)
(****************************************************************************)
THEOREM TreeConnectedAntisymmetric ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), 
           NEW a \in G.node, NEW b \in G.node,
           AreConnectedIn(a, b, G), AreConnectedIn(b, a, G)
    PROVE  a = b 
<1>1. PICK p \in Path(G) : p[1] = a /\ p[Len(p)] = b 
  BY DEF AreConnectedIn 
<1>2. PICK q \in Path(G) : q[1] = b /\ q[Len(q)] = a 
  BY DEF AreConnectedIn 
<1>. p \in Seq(G.node) \ { <<>> } /\ q \in Seq(G.node) \ { <<>> }
  BY DEF Path 
<1>. DEFINE pq == p \o Tail(q)
<1>3. pq \in Path(G)
  BY <1>1, <1>2, PathConcatenation
<1>4. pq \in SimplePath(G)
  BY <1>3, TreeSimplePath 
<1>5. pq[1] = a /\ pq[Len(pq)] = a 
  BY <1>1, <1>2
<1>6. Len(pq) = 1
  BY <1>4, <1>5 DEF SimplePath 
<1>. QED  BY <1>1, <1>6

(****************************************************************************)
(* A graph consisting of only the root and no edges is a tree.              *)
(****************************************************************************)
THEOREM SingletonIsTreeWithRoot ==
    ASSUME NEW r
    PROVE IsTreeWithRoot([node |-> {r}, edge |-> {}],r)
<1>. DEFINE G == [node |-> {r}, edge |-> {}]
<1>1. IsDirectedGraph(G)
    BY DEF IsDirectedGraph
<1>2. \A n \in G.node : AreConnectedIn(n, r, G)
    <2>. <<r>> \in Path(G)
        BY DEF Path
    <2>. QED BY DEF AreConnectedIn
<1>. QED BY <1>1, <1>2 DEF IsTreeWithRoot, IsDirectedGraph

(****************************************************************************)
(* A tree can be extended by attaching a disjoint tree to a node.           *)
(****************************************************************************)
THEOREM AttachTree ==
    ASSUME NEW G, NEW r, IsTreeWithRoot(G,r), NEW n \in G.node,
           NEW H, NEW s, IsTreeWithRoot(H,s), G.node \cap H.node = {} 
    PROVE  IsTreeWithRoot([node |-> G.node \cup H.node,
                           edge |-> G.edge \cup H.edge \cup {<<s,n>>}], r)
<1>. DEFINE T == [node |-> G.node \cup H.node,
                  edge |-> G.edge \cup H.edge \cup {<<s,n>>}]
<1>1. IsDirectedGraph(T)
  BY DEF IsDirectedGraph, IsTreeWithRoot 
<1>2. r \in T.node
  BY DEF IsTreeWithRoot
<1>3. ASSUME NEW e \in T.edge PROVE e[1] # r
  BY DEF IsTreeWithRoot, IsDirectedGraph
<1>4. ASSUME NEW e \in T.edge, NEW f \in T.edge, e[1] = f[1]
      PROVE  e = f
  BY <1>4 DEF IsTreeWithRoot, IsDirectedGraph 
<1>5. ASSUME NEW nd \in T.node
      PROVE AreConnectedIn(nd, r, T)
  <2>1. CASE nd \in G.node
    <3>1. PICK p \in Path(G) : p[1] = nd /\ p[Len(p)] = r 
      BY <2>1 DEF IsTreeWithRoot, AreConnectedIn
    <3>2. p \in Path(T)
      BY DEF Path 
    <3>. QED  BY <3>1, <3>2 DEF AreConnectedIn 
  <2>2. CASE nd \in H.node
    <3>1. PICK p \in Path(H) : p[1] = nd /\ p[Len(p)] = s
      BY <2>2 DEF IsTreeWithRoot, AreConnectedIn 
    <3>2. PICK q \in Path(G) : q[1] = n /\ q[Len(q)] = r 
      BY DEF IsTreeWithRoot, AreConnectedIn 
    <3>. p \in Seq(H.node) \ { <<>> } /\ q \in Seq(G.node) \ { <<>> }
      BY DEF Path 
    <3>. DEFINE pq == p \o q
    <3>3. pq \in Seq(T.node) \ { <<>> }
      BY <3>1, <3>2
    <3>4. ASSUME NEW i \in 1 .. Len(pq)-1 
          PROVE  << pq[i], pq[i+1] >> \in T.edge 
      <4>1. CASE i \in 1 .. Len(p)-1
        BY <4>1 DEF Path 
      <4>2. CASE i = Len(p)
        BY <3>1, <3>2, <4>2
      <4>3. CASE i \in Len(p)+1 .. Len(pq)-1
        BY <4>3, i - Len(p) \in 1 .. Len(q)-1 DEF Path 
      <4>. QED  BY <4>1, <4>2, <4>3 
    <3>5. pq[1] = nd /\ pq[Len(pq)] = r
      BY <3>1, <3>2
    <3>. HIDE DEF pq, T
    <3>. QED  BY <3>3, <3>4, <3>5 DEF AreConnectedIn, Path 
  <2>. QED  BY <2>1, <2>2
<1>. QED  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IsTreeWithRoot 

(****************************************************************************)
(* In particular, a tree can be extended by a new node that becomes a leaf. *)
(****************************************************************************)
THEOREM AddLeafToTree == 
    ASSUME NEW G, NEW r, NEW leaf, NEW parent,
           IsTreeWithRoot(G,r), leaf \notin G.node, parent \in G.node
    PROVE  IsTreeWithRoot([node |-> G.node \cup {leaf}, 
                           edge |-> G.edge \cup {<<leaf, parent>>}], r)
<1>. DEFINE H == [node |-> {leaf}, edge |-> {}]
<1>1. IsTreeWithRoot(H, leaf)
  BY SingletonIsTreeWithRoot
<1>2. G.node \cap H.node = {}
  OBVIOUS 
<1>3. IsTreeWithRoot([node |-> G.node \cup H.node,
                      edge |-> G.edge \cup H.edge \cup {<<leaf, parent>>}], r)
  <2>. HIDE DEF H 
  <2>. QED  BY <1>1, <1>2, AttachTree 
<1>. QED  BY <1>3, Zenon

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
<1>. DEFINE S == { n \in G.node : AreConnectedIn(n, nd, G) }
            T == G.node \ S 
            E == G.edge \cap (T \X T)
            SG == [node |-> T, edge |-> E]
<1>1. IsDirectedGraph(SG)
  BY DEF IsDirectedGraph
<1>2. r \in SG.node
  <2>1. r \in G.node /\ AreConnectedIn(nd, r, G)
    BY DEF IsTreeWithRoot 
  <2>2. ~ AreConnectedIn(r, nd, G)
    BY <2>1, TreeConnectedAntisymmetric
  <2>. QED  BY <2>1, <2>2
<1>3. ASSUME NEW e \in SG.edge
      PROVE  /\ e[1] # r 
             /\ \A f \in SG.edge : e[1] = f[1] => e = f 
  BY DEF IsTreeWithRoot 
<1>4. ASSUME NEW n \in SG.node
      PROVE  AreConnectedIn(n, r, SG)
  <2>1. PICK p \in Path(G) : p[1] = n /\ p[Len(p)] = r 
    BY DEF IsTreeWithRoot, AreConnectedIn 
  <2>. p \in Seq(G.node) \ { <<>> }
    BY DEF Path 
  <2>2. p \in Seq(T)
    <3>1. SUFFICES ASSUME NEW i \in 1 .. Len(p), AreConnectedIn(p[i], nd, G)
                   PROVE  FALSE 
      OBVIOUS     
    <3>2. SubSeq(p, 1, i) \in Path(G)
      BY SubPath
    <3>3. AreConnectedIn(n, p[i], G)
      BY <2>1, <3>2 DEF AreConnectedIn 
    <3>. QED  BY <3>1, <3>3, ConnectedTransitive
  <2>. HIDE DEF T
  <2>3. \A i \in 1 .. Len(p)-1 : <<p[i], p[i+1]>> \in E 
    BY <2>2 DEF Path 
  <2>4. p \in Path(SG)
    BY <2>2, <2>3 DEF Path 
  <2>. QED  BY <2>1, <2>4 DEF AreConnectedIn 
<1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF IsTreeWithRoot 

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
<1>1. leaf # r 
  BY DEF IsTreeWithRoot 
<1>. DEFINE S == {n \in G.node : AreConnectedIn(n, leaf, G)}
            T == G.node \ S 
            E == G.edge \cap (T \X T)
<1>2. IsTreeWithRoot([node |-> T, edge |-> E], r)
  BY <1>1, RemoveSubtree, IsaM("blast")
<1>3. S = {leaf}
  <2>1. leaf \in S 
    BY ConnectedReflexive
  <2>2. ASSUME NEW n \in G.node, AreConnectedIn(n, leaf, G)
        PROVE  n = leaf 
    <3>1. PICK p \in Path(G) : p[1] = n /\ p[Len(p)] = leaf 
      BY <2>2 DEF AreConnectedIn 
    <3>2. Len(p)-1 \notin 1 .. Len(p)-1
      BY <3>1 DEF Path, Predecessors
    <3>. QED  BY <3>1, <3>2 DEF Path
  <2>. QED  BY <2>1, <2>2
<1>4. E = G.edge \ {<<leaf, parent>>}
  <2>1. E \subseteq G.edge \ {<<leaf, parent>>}
    BY <1>3
  <2>2. ASSUME NEW e \in G.edge, e # <<leaf, parent>> 
        PROVE  e \in E 
    <3>1. PICK a \in G.node, b \in G.node : e = <<a,b>> 
      BY DEF IsTreeWithRoot, IsDirectedGraph 
    <3>2. CASE a \in S  \* a must be `leaf', but it has a unique successor
      BY <1>3, <2>2, <3>1, <3>2 DEF IsTreeWithRoot 
    <3>3. CASE b \in S  \* b must be `leaf', but it has no predecessor
      BY <1>3, <3>1, <3>3 DEF Predecessors 
    <3>. QED  BY <3>1, <3>2, <3>3
  <2>. QED  BY <2>1, <2>2 
<1>. HIDE DEF E, S 
<1>. QED  BY <1>2, <1>3, <1>4

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
BY SingletonIsTreeWithRoot DEF Transpose 

THEOREM AttachTransposedTree ==
    ASSUME NEW G, NEW r, IsDirectedGraph(G), IsTreeWithRoot(Transpose(G), r),
           NEW H, NEW s, IsDirectedGraph(H), IsTreeWithRoot(Transpose(H), s),
           G.node \cap H.node = {}, NEW n \in G.node
    PROVE  IsTreeWithRoot(Transpose([node |-> G.node \cup H.node,
                                     edge |-> G.edge \cup H.edge \cup {<<n,s>>}]), r)
<1>. DEFINE GN == G.node    GE == G.edge    TGE == {<<e[2], e[1]>> : e \in GE}
            HN == H.node    HE == H.edge    THE == {<<e[2], e[1]>> : e \in HE}
<1>1. /\ G = [node |-> GN, edge |-> GE]
      /\ GE \subseteq GN \X GN
      /\ H = [node |-> HN, edge |-> HE]
      /\ HE \subseteq HN \X HN
  BY DEF IsDirectedGraph 
<1>. HIDE DEF GN, GE, HN, HE 
<1>2. /\ Transpose(G) = [node |-> GN, edge |-> TGE]
      /\ Transpose(H) = [node |-> HN, edge |-> THE]
  BY <1>1 DEF Transpose 
<1>3. IsTreeWithRoot([node |-> GN \cup HN,
                      edge |-> TGE \cup THE \cup {<<s,n>>}], r)
  BY <1>1, <1>2, AttachTree 
<1>4. {<<e[2], e[1]>> : e \in GE \cup HE \cup {<<n,s>>}} = TGE \cup THE \cup {<<s,n>>}
  BY <1>1
<1>. QED  BY <1>1, <1>3, <1>4 DEF Transpose 

THEOREM AddLeafToTransposedTree == 
    ASSUME NEW G, NEW r, NEW leaf, NEW parent,
           IsDirectedGraph(G), IsTreeWithRoot(Transpose(G),r),
           leaf \notin G.node, parent \in G.node
    PROVE  IsTreeWithRoot(Transpose([node |-> G.node \cup {leaf}, 
                                     edge |-> G.edge \cup {<<parent, leaf>>}]), r)
<1>. DEFINE N == G.node
            E == G.edge
            TE == {<<e[2], e[1]>> : e \in G.edge}
<1>1. /\ G = [node |-> N, edge |-> E]
      /\ E \subseteq N \X N 
  BY DEF IsDirectedGraph 
<1>. HIDE DEF N, E 
<1>2. Transpose(G) = [node |-> N, edge |-> TE]
  BY <1>1 DEF Transpose 
<1>3. IsTreeWithRoot([node |-> N \cup {leaf},
                      edge |-> TE \cup {<<leaf, parent>>}], r)
  BY <1>1, <1>2, AddLeafToTree
<1>4. {<<e[2], e[1]>> : e \in E \cup {<<parent, leaf>>}} = TE \cup {<<leaf, parent>>}
  BY <1>1
<1>. QED  BY <1>1, <1>3, <1>4 DEF Transpose 

THEOREM RemoveTransposedSubtree ==
    ASSUME NEW G, NEW r, IsDirectedGraph(G), IsTreeWithRoot(Transpose(G), r),
           NEW nd \in G.node \ {r}
    PROVE  LET S == {n \in G.node : AreConnectedIn(nd, n, G)}
               T == G.node \ S 
               E == G.edge \cap (T \X T)
           IN  IsTreeWithRoot(Transpose([node |-> T, edge |-> E]), r)
<1>. DEFINE GN == G.node   GE == G.edge    TGE == {<<e[2], e[1]>> : e \in GE}
            S == {n \in GN : AreConnectedIn(nd, n, G)}
            T == GN \ S 
            E == GE \cap (T \X T)
            TG == Transpose(G)
            TS == {n \in TG.node : AreConnectedIn(n, nd, TG)}
            TT == TG.node \ TS 
            TE == TG.edge \cap (TT \X TT)
<1>1. /\ G = [node |-> GN, edge |-> GE]
      /\ GE \subseteq GN \X GN
  BY DEF IsDirectedGraph 
<1>. HIDE DEF GN, GE 
<1>2. TG = [node |-> GN, edge |-> TGE]
  BY <1>1 DEF Transpose 
<1>3. /\ IsTreeWithRoot(TG, r)
      /\ nd \in TG.node \ {r}
  BY <1>1, <1>2
<1>4. IsTreeWithRoot([node |-> TT, edge |-> TE], r)
  BY <1>3, RemoveSubtree, IsaM("blast")
<1>5. T = TT
  BY TransposeAreConnectedIn, AreConnectedInTranspose, <1>1, <1>2
<1>6. {<<e[2], e[1]>> : e \in E} = TE 
  BY <1>1, <1>2, <1>5
<1>7. IsTreeWithRoot(Transpose([node |-> T, edge |-> E]), r)
  <2>. HIDE DEF T, TT, E, TE 
  <2>. QED  BY <1>4, <1>5, <1>6 DEF Transpose 
<1>. QED  BY <1>7 DEF GN, GE 

THEOREM RemoveLeafFromTransposedTree ==
    ASSUME NEW G, IsDirectedGraph(G),
           NEW r, IsTreeWithRoot(Transpose(G),r),
           NEW leaf \in G.node,
           Successors(G, leaf) = {},
           NEW parent \in G.node, <<parent, leaf>> \in G.edge
    PROVE  IsTreeWithRoot(Transpose([node |-> G.node \ {leaf}, 
                                     edge |-> G.edge \ {<<parent, leaf>>}]), r)
<1>. DEFINE N == G.node
            E == G.edge
            TE == {<<e[2], e[1]>> : e \in G.edge}
<1>1. /\ G = [node |-> N, edge |-> E]
      /\ E \subseteq N \X N 
  BY DEF IsDirectedGraph 
<1>. HIDE DEF N, E 
<1>2. /\ Transpose(G) = [node |-> N, edge |-> TE]
      /\ Predecessors(Transpose(G), leaf) = {}
  BY <1>1 DEF Transpose, Predecessors, Successors
<1>3. IsTreeWithRoot([node |-> N \ {leaf},
                      edge |-> TE \ {<<leaf, parent>>}], r)
  BY <1>1, <1>2, RemoveLeafFromTree 
<1>4. {<<e[2], e[1]>> : e \in E \ {<<parent, leaf>>}} = TE \ {<<leaf, parent>>}
  BY <1>1
<1>. QED  BY <1>1, <1>3, <1>4 DEF Transpose 

==============================================================================
