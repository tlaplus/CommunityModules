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
            \/ happenedBefore(clock(log[j]), clock(log[i]))
            \/ concurrent(clock(log[j]), clock(log[i]))

SortCausally(log, clock(_), node(_)) ==
    (*
        Sort the given log based on the vector clock values. The predicates
        clock and node are used to extract the vector clock and node values
        from the log entries.
    *)
    CHOOSE newlog \in 
        { f \in 
            [ 1..Len(log) -> Range(log)] : 
                Range(f) = Range(log) } : 
                    IsCausallyOrdered(newlog, clock)

===============================================================================