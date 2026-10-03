------------------------- MODULE VectorClocksTests -------------------------
EXTENDS VectorClocks, Sequences, Naturals, TLC, Json

ASSUME LET T == INSTANCE TLC IN T!PrintT("VectorClocksTests")

ASSUME IsCausalOrder(<< >>, LAMBDA l: l)
ASSUME IsCausalOrder(<< <<0,0>> >>, LAMBDA l: l)
ASSUME IsCausalOrder(<< <<0,0>>, <<0,1>> >>, LAMBDA l: l) \* happened before
ASSUME IsCausalOrder(<< <<1,0>>, <<0,1>> >>, LAMBDA l: l) \* concurrent

ASSUME IsCausalOrder(<< <<0>>, <<0,1>> >>, LAMBDA l: l) \* happened before
ASSUME IsCausalOrder(<< <<1>>, <<0,1>> >>, LAMBDA l: l) \* concurrent

ASSUME ~IsCausalOrder(<< <<0,1>>, <<0,0>> >>, LAMBDA l: l)

ASSUME ~IsCausalOrder(<< <<1>>, <<0,0>> >>, LAMBDA l: l) \* concurrent

Log ==
    ndJsonDeserialize("tests/VectorClocksTests.ndjson")

VectorClock(l) ==
    l.pkt.vc

Node(l) ==
    \* ToString is a hack to work around the fact that the Json
     \* module deserializes {"0": 42, "1": 23} into the record
     \* [ 0 |-> 42, 1 |-> 23 ] with domain {"0", "1"} and not
     \* into a function with domain {0, 1}.
    ToString(l.node)

ASSUME ~IsCausalOrder(Log, VectorClock)

ASSUME IsCausalOrder(
			CausalOrder(Log, 
						 VectorClock, 
						 Node,
						 LAMBDA vc: DOMAIN vc), 
			VectorClock)

\* CausalOrder is defined via CHOOSE, so its pure counterpart is the set of all
\* logs that it may choose from.
CausalOrderPure(log, clock(_)) ==
    { f \in [ 1..Len(log) -> Range(log)] : 
        Range(f) = Range(log) /\ IsCausalOrder(f, clock) }

\* Node 1 sends a message to node 2 after its first event, and both nodes
\* have one more event that is concurrent with the other node's events.
SmallLog ==
    << [node |-> 1, vc |-> <<1, 0>>],
       [node |-> 2, vc |-> <<0, 1>>],
       [node |-> 2, vc |-> <<1, 2>>],
       [node |-> 1, vc |-> <<2, 0>>] >>

ASSUME \A p \in Permutations(DOMAIN SmallLog) :
    LET log == << SmallLog[p[1]], SmallLog[p[2]], SmallLog[p[3]], SmallLog[p[4]] >>
    IN CausalOrder(log, LAMBDA l: l.vc, LAMBDA l: l.node, LAMBDA vc: DOMAIN vc)
         \in CausalOrderPure(log, LAMBDA l: l.vc)

=============================================================================
