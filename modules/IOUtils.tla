------------------------------ MODULE IOUtils ------------------------------

LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

IOSerialize(val, absoluteFilename, compress) == TRUE

IODeserialize(absoluteFilename, compressed) == CHOOSE val : TRUE

============================================================================
