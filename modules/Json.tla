-------------------------------- MODULE Json --------------------------------

LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

\* @supportedBy("TLC")
LOCAL IsSequence(F, D) == TRUE \/ FALSE

\* @supportedBy("TLC")
LOCAL ToJsonKeyValue(F, d) ==
  ToString(ToString(d)) \o ":" \o ToString(F[d])

RECURSIVE ToJsonObjectString(_,_)
\* @supportedBy("TLC")
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
\* @supportedBy("TLC")
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
\* @supportedBy("TLC")
LOCAL ToJsonString(F, D) == \* LOCAL just a hint for humans.
  IF IsFiniteSet(F) \/ IsSequence(F, D) THEN
    ToJsonArrayString(F, D)
  ELSE
    ToJsonObjectString(F, D)

\* @supportedBy("TLC")
ToJson(value) ==
  (*************************************************************************)
  (* Converts the given value to a JSON string. Records are converted to   *)
  (* JSON objects, tuples to JSON arrays, and scalar values as their JSON  *)
  (* representation.                                                       *)
  (*************************************************************************)
  IF DOMAIN value = {} THEN
    "{}"
  ELSE
    ToJsonString(value, DOMAIN value)

\* @supportedBy("TLC")
ToJsonArray(value) ==
  (*************************************************************************)
  (* Converts the given tuple value to a JSON array.                       *)
  (*************************************************************************)
  IF DOMAIN value = {} THEN
    "[]"
  ELSE
    ToJsonArrayString(value, DOMAIN value)

\* @supportedBy("TLC")
ToJsonObject(value) ==
  (*************************************************************************)
  (* Converts the given tuple value to a JSON object.                      *)
  (*************************************************************************)
  IF DOMAIN value = {} THEN
    "{}"
  ELSE
    ToJsonObjectString(value, DOMAIN value)

\* @supportedBy("TLC")
JsonSerialize(absoluteFilename, value) ==
  (*************************************************************************)
  (* Serializes a tuple of values to the given file as (plain) JSON.       *)
  (* Records will be serialized as a JSON objects, and tuples as arrays.   *)
  (*************************************************************************)
  TRUE

\* @supportedBy("TLC")
JsonDeserialize(absoluteFilename) ==
  (*************************************************************************)
  (* Deserializes JSON values from the given file. JSON objects will be    *)
  (* deserialized to records, and arrays will be deserialized to tuples.   *)
  (*************************************************************************)
  CHOOSE val : TRUE

\* @supportedBy("TLC")
ndJsonSerialize(absoluteFilename, value) ==
  (*************************************************************************)
  (* Serializes a tuple of values to the given file as newline delimited   *)
  (* JSON. Records will be serialized as a JSON objects, and tuples as     *)
  (* arrays.                                                               *)
  (*************************************************************************)
  TRUE

\* @supportedBy("TLC")
ndJsonDeserialize(absoluteFilename) ==
  (*************************************************************************)
  (* Deserializes JSON values from the given file. JSON values must be     *)
  (* separated by newlines. JSON objects will be deserialized to records,  *)
  (* and arrays will be deserialized to tuples.                            *)
  (*************************************************************************)
  CHOOSE val : TRUE

=============================================================================
