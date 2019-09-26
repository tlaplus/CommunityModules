------------------------------- MODULE ShiViz -------------------------------
EXTENDS Integers, Json, Toolbox, TLC

-----------------------------------------------------------------------------

\* Host below is different to the action predicate 
\*   CHOOSE p \in DOMAIN pc : pc[p] # pc'[p]
\* since Host evaluates for states n and n - 1
\* whereas the CHOOSE evalutes for states n and n + 1.
\* This difference is most easily observed by looking
\* at off-by-one difference of the initial state.
LOCAL FnHost ==
    LET host[i \in DOMAIN _TETrace] ==
        (*************************************************************************)
        (* The pc value that has been modified in (the current) state n compared *)
        (* to the predecessor state n-1.                                         *)
        (*************************************************************************)
        IF i = 1 THEN "--"
        ELSE IF _TETrace[i-1].pc = _TETrace[i].pc
                THEN host[i-1] \* pc variable has not changed.
                ELSE CHOOSE p \in DOMAIN _TETrace[i-1].pc :
                            _TETrace[i-1].pc[p] # _TETrace[i].pc[p]
    IN TLCEval(host)

Host == FnHost[_TEPosition]
    
-----------------------------------------------------------------------------

LOCAL clock(n) == 
   [p \in DOMAIN _TETrace[n].pc |-> IF p = FnHost[n] 
                                    THEN 1
                                    ELSE 0]

LOCAL sum(F, G) == 
   [d \in DOMAIN F |-> F[d] + G[d]]

LOCAL FnClock == 
    LET vclock[i \in DOMAIN _TETrace] == 
        IF i = 1
        THEN clock(i)
        ELSE sum(TLCEval(vclock[i-1]), clock(i))
    IN TLCEval(vclock)

Clock ==
   (*************************************************************************)
   (* The pc variable formatted as a Json object as required by ShiViz.     *)
   (*************************************************************************)
   ToJsonObject(FnClock[_TEPosition])

=============================================================================
\* Modification History
\* Last modified Tue Sep 25 17:20:37 PDT 2019 by markus
\* Created Tue Aug 27 13:04:16 PDT 2019 by markus
