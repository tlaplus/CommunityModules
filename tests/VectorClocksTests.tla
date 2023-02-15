------------------------- MODULE VectorClocksTests -------------------------
EXTENDS VectorClocks, Sequences, Naturals, TLC, TLCExt, Json

ASSUME LET T == INSTANCE TLC IN T!PrintT("VectorClocksTests")

Log ==
    ndJsonDeserialize("tests/VectorClocksTests.ndjson")

VectorClock(l) ==
    l.pkt.vc

Node(l) ==
    ToString(l.node)

ASSUME IsCausallyOrdered(Log, VectorClock)

ASSUME IsCausallyOrdered(SortCausally(Log, VectorClock, Node), VectorClock)

=============================================================================
