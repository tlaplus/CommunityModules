---------------------------- MODULE VectorClocks -------------------------------
EXTENDS Naturals, Sequences, Functions

LOCAL concurrent(v1, v2) ==
    \E i,j \in DOMAIN v1: i # j /\ v1[i] < v2[i] /\ v1[j] > v2[j]

LOCAL happenedBefore(v1, v2) ==
    \* A vector clock v1 is said to happen before v2 if for all nodes, 
     \*  x[n] <= y[n]  , and there exists at least one node such that
     \*  x[h] < y[h].
    /\ \A i \in DOMAIN v1: v1[i] <= v2[i]
    /\ \E i \in DOMAIN v1: v1[i]  < v2[i]

IsCausallyOrdered(log, clock(_)) ==
    \A i \in 1..Len(log) :
        \A j \in 1..(i - 1) :
            \* Align the vector clocks to the same domain (mapping
             \* missing values to 0).  A node gradually learns about
             \* other nodes, so its clock domain expands over time.
            LET Fill(c, D) == 
                    [ d \in D |-> IF d \in DOMAIN c THEN c[d] ELSE 0 ]
                D   == DOMAIN clock(log[i]) \cup DOMAIN clock(log[j])
                vci == Fill(clock(log[i]), D)
                vcj == Fill(clock(log[j]), D)
            IN happenedBefore(vcj, vci) \/ concurrent(vcj, vci)

SortCausally(log, clock(_), node(_), domain(_)) ==
    (*
        Sort the provided log by the vector clock values indicated on each line
        of the log. This operator cannot accommodate "hidden" events, meaning
        events that are excluded from the log. The vector clocks must be
        continuous without any gaps.
        
        The predicates clock, node, and domain equals the vector clock from
        a log entry, the node's clock value, and the clock's domain, i.e., the
        nodes for which the clock has values.
        
        Imagine a log containing lines such as:
        
        	[pkt |-> 
        		[vc |-> 
        			[1 |-> 20, 
        			 0 |-> 10,
        			 3 |-> 16, 
        			 7 |-> 21, 
        			 4 |-> 10, 
        			 6 |-> 21]],
        	 node |-> 5,
			 ...
		    ]
		 
		 SortCausally(log, 
					 	LAMBDA line: line.pkt.vc,
					 	LAMBDA line: line.node,
						LAMBDA vc : DOMAIN vc)
    *)
    CHOOSE newlog \in 
        { f \in 
            [ 1..Len(log) -> Range(log)] : 
                Range(f) = Range(log) } : 
                    IsCausallyOrdered(newlog, clock)

===============================================================================