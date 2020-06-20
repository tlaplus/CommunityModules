------------ MODULE IncompleteStates -------------
EXTENDS TLCExt

VARIABLE u, v, w
vars == <<u,v,w>>

Init ==
  /\ u = 42
  /\ Trace
  /\ v = 23
  /\ w = TRUE
       
Next ==
  /\ UNCHANGED vars
===========================================