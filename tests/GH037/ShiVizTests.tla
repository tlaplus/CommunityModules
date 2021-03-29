\* :0:__trace_var_161703600296656000:Host"$!@$!@$!@$!@$!"
\* :0:__trace_var_161703600296658000:_TETrace"$!@$!@$!@$!@$!"
---- MODULE ShiVizTests ----
EXTENDS TLC, ShiViz, Toolbox

VARIABLES StorageValues, pc

vars == << StorageValues, pc >>

CONSTANTS Clients, Database, Cache

Storages == {Database, Cache}

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
ClientA, ClientB
----

\* MV CONSTANT definitions Clients
const_161703600298862000 == 
{ClientA, ClientB}
----

def_ov_161703600298863000 == 
    <<
    ([StorageValues |-> (Database :> 0 @@ Cache :> 0),pc |-> (ClientA :> "WriteDatabase" @@ ClientB :> "WriteDatabase")]),
    ([StorageValues |-> (Database :> ClientA @@ Cache :> 0),pc |-> (ClientA :> "WriteCache" @@ ClientB :> "WriteDatabase")]),
    ([StorageValues |-> (Database :> ClientB @@ Cache :> 0),pc |-> (ClientA :> "WriteCache" @@ ClientB :> "WriteCache")]),
    ([StorageValues |-> (Database :> ClientB @@ Cache :> ClientB),pc |-> (ClientA :> "WriteCache" @@ ClientB :> "Done")]),
    ([StorageValues |-> (Database :> ClientB @@ Cache :> ClientA),pc |-> (ClientA :> "Done" @@ ClientB :> "Done")])
    >>
----


\* TRACE EXPLORER variable declaration @traceExploreExpressions
VARIABLES __trace_var_161703600296656000,__trace_var_161703600296658000
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions:0
trace_def_161703600296655000 ==
Host
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions:1
trace_def_161703600296657000 ==
_TETrace
----

\* TRACE Sub-Action definition 0
next_sa_0 ==
    (
        /\ StorageValues = (
                (Database :> 0 @@ Cache :> 0)
            )
        /\ pc = (
                (ClientA :> "WriteDatabase" @@ ClientB :> "WriteDatabase")
            )
        /\ StorageValues' = (
                (Database :> ClientA @@ Cache :> 0)
            )
        /\ pc' = (
                (ClientA :> "WriteCache" @@ ClientB :> "WriteDatabase")
            )
        /\ __trace_var_161703600296656000' = (
            trace_def_161703600296655000
            )'
        /\ __trace_var_161703600296658000' = (
            trace_def_161703600296657000
            )'
    )

\* TRACE Sub-Action definition 1
next_sa_1 ==
    (
        /\ StorageValues = (
                (Database :> ClientA @@ Cache :> 0)
            )
        /\ pc = (
                (ClientA :> "WriteCache" @@ ClientB :> "WriteDatabase")
            )
        /\ StorageValues' = (
                (Database :> ClientB @@ Cache :> 0)
            )
        /\ pc' = (
                (ClientA :> "WriteCache" @@ ClientB :> "WriteCache")
            )
        /\ __trace_var_161703600296656000' = (
            trace_def_161703600296655000
            )'
        /\ __trace_var_161703600296658000' = (
            trace_def_161703600296657000
            )'
    )

\* TRACE Sub-Action definition 2
next_sa_2 ==
    (
        /\ StorageValues = (
                (Database :> ClientB @@ Cache :> 0)
            )
        /\ pc = (
                (ClientA :> "WriteCache" @@ ClientB :> "WriteCache")
            )
        /\ StorageValues' = (
                (Database :> ClientB @@ Cache :> ClientB)
            )
        /\ pc' = (
                (ClientA :> "WriteCache" @@ ClientB :> "Done")
            )
        /\ __trace_var_161703600296656000' = (
            trace_def_161703600296655000
            )'
        /\ __trace_var_161703600296658000' = (
            trace_def_161703600296657000
            )'
    )

\* TRACE Sub-Action definition 3
next_sa_3 ==
    (
        /\ StorageValues = (
                (Database :> ClientB @@ Cache :> ClientB)
            )
        /\ pc = (
                (ClientA :> "WriteCache" @@ ClientB :> "Done")
            )
        /\ StorageValues' = (
                (Database :> ClientB @@ Cache :> ClientA)
            )
        /\ pc' = (
                (ClientA :> "Done" @@ ClientB :> "Done")
            )
        /\ __trace_var_161703600296656000' = (
            trace_def_161703600296655000
            )'
        /\ __trace_var_161703600296658000' = (
            trace_def_161703600296657000
            )'
    )

\* TRACE Sub-Action definition 4
next_sa_4 ==
    (
        /\ StorageValues = (
                (Database :> ClientB @@ Cache :> ClientA)
            )
        /\ pc = (
                (ClientA :> "Done" @@ ClientB :> "Done")
            )
        /\ StorageValues' = (
                (Database :> ClientB @@ Cache :> ClientA)
            )
        /\ pc' = (
                (ClientA :> "Done" @@ ClientB :> "Done")
            )
        /\ __trace_var_161703600296656000' = (
            trace_def_161703600296655000
            )'
        /\ __trace_var_161703600296658000' = (
            trace_def_161703600296657000
            )'
    )

\* TRACE Action Constraint definition traceExploreActionConstraint
action_constr_161703600296661000 ==
<<
next_sa_0,
next_sa_1,
next_sa_2,
next_sa_3,
next_sa_4
>>[TLCGet("level")]
----

\* TRACE INIT definition traceExploreInit
init_161703600296659000 ==
    /\ StorageValues = (
            (Database :> 0 @@ Cache :> 0)
        )
    /\ pc = (
            (ClientA :> "WriteDatabase" @@ ClientB :> "WriteDatabase")
        )
    /\ __trace_var_161703600296656000 = (
            trace_def_161703600296655000
        )
    /\ __trace_var_161703600296658000 = (
            trace_def_161703600296657000
        )

----

\* TRACE NEXT definition traceExploreNext
next_161703600296660000 ==
    \/ next_sa_0
    \/ next_sa_1
    \/ next_sa_2
    \/ next_sa_3
    \/ next_sa_4


\* PROPERTY definition
_prop ==
~<>[](
    StorageValues = (
    (Database :> ClientB @@ Cache :> ClientA)
    )    /\
    pc = (
    (ClientA :> "Done" @@ ClientB :> "Done")
    )
)
----

=============================================================================
\* Modification History
\* Created Mon Mar 29 09:40:02 PDT 2021 by markus
