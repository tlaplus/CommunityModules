------------------------------- MODULE ShiViz -------------------------------
EXTENDS Integers, Json, Toolbox

-----------------------------------------------------------------------------

\* Host below is different to the action predicate 
\*   CHOOSE p \in DOMAIN pc : pc[p] # pc'[p]
\* since Host evaluates for states n and n - 1
\* whereas the CHOOSE evalutes for states n and n + 1.
\* This difference is most easily observed by looking
\* at off-by-one difference of the initial state.
LOCAL FnHost[i \in DOMAIN _TETrace] ==
   (*************************************************************************)
   (* The pc value that has been modified in (the current) state n compared *)
   (* to the predecessor state n-1.                                         *)
   (*************************************************************************)
   IF i = 1 THEN "--"
   ELSE IF _TETrace[i-1].pc = _TETrace[i].pc
        THEN FnHost[i-1] \* pc variable has not changed.
        ELSE CHOOSE p \in DOMAIN _TETrace[i-1].pc :
                      _TETrace[i-1].pc[p] # _TETrace[i].pc[p]

Host == FnHost[_TEPosition]
    
-----------------------------------------------------------------------------

LOCAL clock(n) == 
   [p \in DOMAIN _TETrace[n].pc |-> IF p = FnHost[n] 
                                    THEN 1
                                    ELSE 0]

LOCAL sum(F, G) == 
   [d \in DOMAIN F |-> F[d] + G[d]]

LOCAL FnClock[i \in DOMAIN _TETrace] == 
   IF i = 1
   THEN clock(i)
   ELSE sum(FnClock[i-1], clock(i))

Clock ==
   (*************************************************************************)
   (* The pc variable formatted as a Json object as required by ShiViz.     *)
   (*************************************************************************)
   ToJsonObject(FnClock[_TEPosition])

=============================================================================
\* Modification History
\* Last modified Tue Aug 27 17:20:37 PDT 2019 by markus
\* Created Tue Aug 27 13:04:16 PDT 2019 by markus
