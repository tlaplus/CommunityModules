-------------------------------- MODULE Json --------------------------------

LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

LOCAL ToJsonKeyValue(F, d) == 
  ToString(ToString(d)) \o ":" \o ToString(F[d])

RECURSIVE ToJson(_,_)
LOCAL ToJson(F, D) == \* LOCAL just a hint for humans.
  LET d == CHOOSE d \in D: TRUE
  IN IF D = DOMAIN F
     THEN "{" \o ToJsonKeyValue(F, d) \o IF D \ {d} = {}
                                         THEN "}"
                                         ELSE ToJson(F, D \ {d})
     ELSE ", " \o ToJsonKeyValue(F, d) \o IF D \ {d} = {}
                                          THEN "}" 
                                          ELSE ToJson(F, D \ {d})

ToJsonObject(F) ==
  (*************************************************************************)
  (* This equals a string that is the Json representation of the given     *)
  (* function F s.t. DOMAIN F \subseteq Nat and Range(F) \subseteq STRING  *)
  (* with Range(g) == { g[x] : x \in DOMAIN g }.                           *)
  (*************************************************************************)
  IF DOMAIN F = {} 
  THEN "{}"
  ELSE ToJson(F, DOMAIN F)


=============================================================================
