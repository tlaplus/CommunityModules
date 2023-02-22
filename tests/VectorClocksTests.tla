------------------------- MODULE VectorClocksTests -------------------------
EXTENDS VectorClocks, Sequences, Naturals, TLC, Json

ASSUME LET T == INSTANCE TLC IN T!PrintT("VectorClocksTests")

ASSUME IsCausallyOrdered(<< >>, LAMBDA l: l)
ASSUME IsCausallyOrdered(<< <<0,0>> >>, LAMBDA l: l)
ASSUME IsCausallyOrdered(<< <<0,0>>, <<0,1>> >>, LAMBDA l: l) \* happened before
ASSUME IsCausallyOrdered(<< <<1,0>>, <<0,1>> >>, LAMBDA l: l) \* concurrent

ASSUME IsCausallyOrdered(<< <<0>>, <<0,1>> >>, LAMBDA l: l) \* happened before
ASSUME IsCausallyOrdered(<< <<1>>, <<0,1>> >>, LAMBDA l: l) \* concurrent

ASSUME ~IsCausallyOrdered(<< <<0,1>>, <<0,0>> >>, LAMBDA l: l)

ASSUME ~IsCausallyOrdered(<< <<1>>, <<0,0>> >>, LAMBDA l: l) \* concurrent

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

ASSUME ~IsCausallyOrdered(Log, VectorClock)

ASSUME IsCausallyOrdered(
			SortCausally(Log, 
						 VectorClock, 
						 Node,
						 LAMBDA vc: DOMAIN vc), 
			VectorClock)

=============================================================================
