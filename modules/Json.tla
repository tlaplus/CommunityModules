-------------------------------- MODULE Json --------------------------------

LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

LOCAL IsSequence(F, D) == TRUE \/ FALSE

LOCAL ToJsonKeyValue(F, d) ==
  ToString(ToString(d)) \o ":" \o ToString(F[d])

RECURSIVE ToJsonObjectString(_,_)
LOCAL ToJsonObjectString(F, D) == \* LOCAL just a hint for humans.
  LET d == CHOOSE d \in D: TRUE
  IN IF D = DOMAIN F
     THEN "{" \o ToJsonKeyValue(F, d) \o IF D \ {d} = {}
                                         THEN "}"
                                         ELSE ToJsonObjectString(F, D \ {d})
     ELSE ", " \o ToJsonKeyValue(F, d) \o IF D \ {d} = {}
                                          THEN "}"
                                          ELSE ToJsonObjectString(F, D \ {d})

RECURSIVE ToJsonArrayString(_,_)
LOCAL ToJsonArrayString(F, D) == \* LOCAL just a hint for humans.
  LET d == CHOOSE d \in D: TRUE
  IN IF D = DOMAIN F
     THEN "[" \o ToString(F[d]) \o IF D \ {d} = {}
                                   THEN "]"
                                   ELSE ToJsonArrayString(F, D \ {d})
     ELSE ", " \o ToString(F[d]) \o IF D \ {d} = {}
                                    THEN "]"
                                    ELSE ToJsonArrayString(F, D \ {d})

RECURSIVE ToJsonString(_,_)
LOCAL ToJsonString(F, D) == \* LOCAL just a hint for humans.
  IF IsFiniteSet(F) \/ IsSequence(F, D) THEN
    ToJsonArrayString(F, D)
  ELSE
    ToJsonObjectString(F, D)

(*************************************************************************)
(* Converts the given value to a JSON string. Records are converted to   *)
(* JSON objects, tuples to JSON arrays, and scalar values as their JSON  *)
(* representation.                                                       *)
(*************************************************************************)
ToJson(value) ==
  IF DOMAIN value = {} THEN
    "{}"
  ELSE
    ToJsonString(value, DOMAIN value)

(*************************************************************************)
(* Converts the given tuple value to a JSON array.                       *)
(*************************************************************************)
ToJsonArray(value) ==
  IF DOMAIN value = {} THEN
    "[]"
  ELSE
    ToJsonArrayString(value, DOMAIN value)

(*************************************************************************)
(* Converts the given tuple value to a JSON object.                      *)
(*************************************************************************)
ToJsonObject(value) ==
  IF DOMAIN value = {} THEN
    "{}"
  ELSE
    ToJsonObjectString(value, DOMAIN value)

(*************************************************************************)
(* Serializes a tuple of values to the given file as (plain) JSON.       *)
(* Records will be serialized as a JSON objects, and tuples as arrays.   *)
(*************************************************************************)
JsonSerialize(absoluteFilename, value) ==
  TRUE

(*************************************************************************)
(* Deserializes JSON values from the given file. JSON objects will be    *)
(* deserialized to records, and arrays will be deserialized to tuples.   *)
(*************************************************************************)
JsonDeserialize(absoluteFilename) ==
  CHOOSE val : TRUE

(*************************************************************************)
(* Serializes a tuple of values to the given file as newline delimited   *)
(* JSON. Records will be serialized as a JSON objects, and tuples as     *)
(* arrays.                                                               *)
(*************************************************************************)
ndJsonSerialize(absoluteFilename, value) ==
  TRUE

(*************************************************************************)
(* Deserializes JSON values from the given file. JSON values must be     *)
(* separated by newlines. JSON objects will be deserialized to records,  *)
(* and arrays will be deserialized to tuples.                            *)
(*************************************************************************)
ndJsonDeserialize(absoluteFilename) ==
  CHOOSE val : TRUE

=============================================================================
