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
(* Values must be finite and encodable: integers within TLC's range and    *)
(* strings of valid Unicode.  Set elements and function arguments must be  *)
(* comparable by TLC for FromCBOR(ToCBOR(v)) = v to hold.  Deep nesting    *)
(* can exhaust the JVM stack, which a larger -Xss setting can relieve.     *)
(***************************************************************************)

LOCAL INSTANCE TLC

(***************************************************************************)
(* The CBOR encoding of value as a sequence of integers in 0..255, one     *)
(* per byte.  Sets use tag 258, model values tag 39, and functions that    *)
(* are neither sequences nor records tag 33000 (registered with IANA).     *)
(* Equal values give identical bytes.  TLC reports an error if value       *)
(* cannot be encoded.                                                      *)
(***************************************************************************)
ToCBOR(value) ==
  Assert(FALSE, "ToCBOR needs CommunityModules.jar on TLC's classpath.")

(***************************************************************************)
(* The TLA+ value of the CBOR data item in bytes, a sequence of integers   *)
(* in 0..255.  TLC reports an error for malformed input and for anything   *)
(* it cannot represent, such as floats or a model value it does not know.  *)
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
(* FromCBOR applied to the bytes of the file absoluteFilename.  A          *)
(* definition without parameters is constant-level, so TLC reuses its      *)
(* value instead of reading the file again in each state.                  *)
(***************************************************************************)
CBORDeserialize(absoluteFilename) ==
  Assert(FALSE, "CBORDeserialize needs CommunityModules.jar on TLC's classpath.")

=============================================================================
