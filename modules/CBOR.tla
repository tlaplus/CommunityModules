-------------------------------- MODULE CBOR --------------------------------
(***************************************************************************)
(* Encodes TLA+ values as CBOR (RFC 8949) and decodes them back.             *)
(* CBORSerialize and CBORDeserialize exchange values through files.         *)
(* Public ToCBOR and FromCBOR work in memory, without file I/O.             *)
(* ToCBOR returns a sequence of integers in 0..255, one per encoded byte.   *)
(* Use its length to check message sizes, or FromCBOR to interpret bytes.  *)
(*                                                                         *)
(* In a module that uses CBOR:                                              *)
(*   EXTENDS Naturals, Sequences, CBOR                                     *)
(*   Message == [id |-> 1, payload |-> <<TRUE, FALSE>>]                    *)
(*   Fits == Len(ToCBOR(Message)) <= 1024                                  *)
(*   Decoded == FromCBOR(<<130, 1, 245>>)   \* equals <<1, TRUE>>         *)
(*                                                                         *)
(* For files, using the same imports and Message definition:               *)
(*   WriteMessage == CBORSerialize("/tmp/message.cbor", Message)           *)
(*   ReadMessage == CBORDeserialize("/tmp/message.cbor")                   *)
(*                                                                         *)
(* Requires CommunityModules.jar or CommunityModules-deps.jar on TLC's    *)
(* classpath. See README.md for setup.                                     *)
(* Sets and function domains must be finite and enumerable by TLC.        *)
(* Integers must fit TLC's range, and strings must be valid Unicode.       *)
(* Decoding reuses existing model values only.                             *)
(* Set elements and function domain elements must be TLC-comparable for    *)
(* round trips. FromCBOR rejects the encoding of {1, "a"}.                 *)
(* Unsupported or malformed inputs fail. Deep nesting can exhaust the      *)
(* JVM stack. See docs/CBOR.md in this repository for the full contract.   *)
(***************************************************************************)

LOCAL INSTANCE TLC

(***************************************************************************)
(* The CBOR encoding of value as a sequence of integers in 0..255, one per *)
(* byte.  If value cannot be encoded (an infinite set, an operator,       *)
(* or a string that is not valid Unicode), TLC reports an error.          *)
(***************************************************************************)
ToCBOR(value) ==
  Assert(FALSE, "ToCBOR needs CommunityModules.jar on TLC's classpath.")

(***************************************************************************)
(* The TLA+ value of the CBOR data item in bytes, a sequence of integers   *)
(* in 0..255.                                                              *)
(***************************************************************************)
FromCBOR(bytes) ==
  Assert(FALSE, "FromCBOR needs CommunityModules.jar on TLC's classpath.")

(***************************************************************************)
(* Writes the bytes of ToCBOR(value) to the file absoluteFilename and      *)
(* equals TRUE.  Creates missing parent directories and replaces an        *)
(* existing file.  If value cannot be encoded, TLC reports an error and    *)
(* leaves the file untouched.                                              *)
(***************************************************************************)
CBORSerialize(absoluteFilename, value) ==
  Assert(FALSE, "CBORSerialize needs CommunityModules.jar on TLC's classpath.")

(***************************************************************************)
(* FromCBOR applied to the bytes of the file absoluteFilename.             *)
(***************************************************************************)
CBORDeserialize(absoluteFilename) ==
  Assert(FALSE, "CBORDeserialize needs CommunityModules.jar on TLC's classpath.")

=============================================================================
