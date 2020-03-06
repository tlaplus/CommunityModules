-------------------------------- MODULE Json --------------------------------

LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

ToJson(value) ==
  (*************************************************************************)
  (* Converts the given value to a JSON string. Records are converted to   *)
  (* JSON objects, tuples to JSON arrays, and scalar values as their JSON  *)
  (* representation.                                                       *)
  (*************************************************************************)
  ""

ToJsonArray(value) ==
  (*************************************************************************)
  (* Converts the given tuple value to a JSON array.                       *)
  (*************************************************************************)
  "[]"

ToJsonObject(F) ==
  (*************************************************************************)
  (* Converts the given tuple value to a JSON object.                      *)
  (*************************************************************************)
  "{}"

JsonSerialize(absoluteFilename, value) ==
  (*************************************************************************)
  (* Serializes a tuple of values to the given file as newline delimited   *)
  (* JSON. Records will be serialized as a JSON objects, and tuples as     *)
  (* arrays.                                                               *)
  (*************************************************************************)
  TRUE

JsonDeserialize(absoluteFilename) ==
  (*************************************************************************)
  (* Deserializes JSON values from the given file. JSON values must be     *)
  (* separated by newlines. JSON objects will be deserialized to records,  *)
  (* and arrays will be deserialized to tuples.                            *)
  (*************************************************************************)
  CHOOSE val : TRUE

=============================================================================
