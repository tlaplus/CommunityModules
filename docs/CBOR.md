# CBOR encoding reference

The `CBOR` module encodes TLA+ values as [CBOR, defined by RFC 8949](https://www.rfc-editor.org/rfc/rfc8949.html), and decodes CBOR into TLC values. The rules below define this module's encoding contract.

All four public operators require the CommunityModules Java overrides on TLC's classpath, including `tlc2.overrides.CBOR`. The TLA+ definitions report an error when the overrides are absent. The repository [README](../README.md#how-to-use-it) describes library and classpath setup.

## Operators

| Operator | Result and effects |
| --- | --- |
| `ToCBOR(value)` | The encoding of `value` as a sequence of integers in `0..255`, one per byte. No file I/O. |
| `FromCBOR(bytes)` | The TLC value represented by one CBOR data item. `bytes` is a sequence of integers in `0..255`. No file I/O. |
| `CBORSerialize(absoluteFilename, value)` | Writes the same bytes as `ToCBOR(value)` and returns `TRUE`. Creates missing parent directories and replaces an existing file. |
| `CBORDeserialize(absoluteFilename)` | Reads a file and decodes its bytes with the same rules as `FromCBOR`. |

`FromCBOR` also accepts functions that TLC can convert to sequences, such as `[i \in 1..n |-> b[i]]`. The file operators take a filename string. `CBORSerialize` encodes the entire value before it touches the file, so an encoding failure leaves an existing file unchanged. A file I/O failure reports an error.

### In-memory expressions

The public `ToCBOR` operator supports encoded message-size checks without temporary files. The public `FromCBOR` operator interprets byte inputs directly, including byte sequences held in model state.

```tla
EXTENDS Naturals, Sequences, CBOR

Message == [id |-> 1, payload |-> <<TRUE, FALSE>>]
FitsPacket(message, maxBytes) == Len(ToCBOR(message)) <= maxBytes
Fits == FitsPacket(Message, 1024)
Decoded == FromCBOR(<<130, 1, 245>>)  \* equals <<1, TRUE>>
RoundTrip == FromCBOR(ToCBOR(Message)) = Message
```

`Len(ToCBOR(message))` counts CBOR bytes, not characters or transport framing bytes. `Naturals` supplies `<=`, and `Sequences` supplies `Len`.

### File expressions

The file operators exchange values with external programs or load CBOR fixtures.

```tla
EXTENDS CBOR

Message == [id |-> 1, payload |-> <<TRUE, FALSE>>]
WriteMessage == CBORSerialize("/tmp/message.cbor", Message)
ReadMessage == CBORDeserialize("/tmp/message.cbor")
```

The read expression requires an existing file. A zero-argument definition such as `ReadMessage` is constant-level, so TLC reads the file once before model checking. These definitions do not establish an execution order between the write and the read.

## Encoding types and tags

For supported values, values that TLC considers equal produce identical bytes, regardless of their internal Java representation or string interning order.

| TLA+ value | CBOR representation |
| --- | --- |
| Integer | Integer, major type 0 for nonnegative values or major type 1 for negative values. |
| `TRUE`, `FALSE` | CBOR `true`, `false`. |
| String | UTF-8 text string. |
| Model value | Tag 39 around its name as a text string. |
| Finite set | Tag 258 around an array of its elements. |
| Function `f` with `DOMAIN f = 1..n` | Array of `f[1]`, ..., `f[n]`. This includes sequences, tuples, and the empty function. |
| Function with a nonempty domain of strings, a record | Map from each domain element `x` to `f[x]`. |
| Other finite function | Tag 33000 around an array of two-element arrays `[x, f[x]]`, one for each domain element `x`. |

The [IANA CBOR tag registry](https://www.iana.org/assignments/cbor-tags/cbor-tags.xhtml) lists tag 39, "Identifier", tag 258, "Mathematical finite set", and tag 33000, "TLA+ function as an array of [argument, value] pairs". The two-element arrays in tag 33000 are CBOR arrays, not TLA+ record syntax.

### Function representation follows the domain

The encoding depends on the function's domain, not how the function was written in TLA+. For `[x \in S |-> 0]`, the representations are:

| Domain `S` | Representation |
| --- | --- |
| `{}` | Empty array. |
| `1..3` | Array. |
| `{"a"}` | Map with a text key. |
| `{1, 3}` | Tag 33000 with argument-value pairs. |
| A nonempty set of model values | Tag 33000 with argument-value pairs. |

A variable that holds a function can change CBOR representation between states. The empty record encodes as an empty array. A consumer of an arbitrary TLA+ function must account for arrays, maps, and tag 33000. Sequences remain arrays. Other functions that are not records use tag 33000.

### Deterministic ordering and widths

The encoder sorts map keys by unsigned lexicographic order of their complete encoded bytes, as in [RFC 8949, section 4.2.1](https://www.rfc-editor.org/rfc/rfc8949.html#section-4.2.1). It uses the same ordering for set elements and for arguments in tag 33000 arrays. Sequence elements retain their sequence order.

For example, `10` precedes `100`, which precedes `-1`, because their encodings are `0a`, `18 64`, and `20`. This is not numeric order. It is also not the length-first ordering in [RFC 7049, section 3.9](https://www.rfc-editor.org/rfc/rfc7049.html#section-3.9), which puts `-1` before `100`.

Integers, tags, and lengths use their shortest available argument widths. All lengths are definite. The encoder removes duplicate representations of equal set elements, so internal duplicates do not change a set's encoding.

## Interoperability

The encoder emits CBOR maps only for records with string keys. Such maps fit native dictionaries or structures with string keys. Sequences use arrays, and other functions use tag 33000 rather than maps with arbitrary keys.

Arbitrary map keys do not fit every language's native dictionary representation. For example, an array-valued map key can fail when fxamacker/cbor decodes it into a Go map because Go slices cannot be map keys. JavaScript objects convert their keys to strings. The tagged array of pairs preserves function arguments without requiring a native dictionary to support them as keys. A consumer still needs to interpret the module's tags.

Foreign producers need not sort set elements, map keys, or function pairs for these decoders. They must follow this module's ordering and width rules to produce byte-identical output.

A library option called "canonical" is not sufficient evidence of compatibility. Map-key sorting alone does not sort the pairs inside tag 33000. For shortest-form text keys, bytewise and length-first map ordering agree, but those orderings differ for general set elements and function arguments. Python cbor2's canonical set encoding uses length-first ordering, which can differ from this module's ordering. Library behavior can vary with versions and options. The module's rules above are authoritative for byte-identical output.

## Decoder acceptance and rejection

`FromCBOR` and `CBORDeserialize` decode exactly one CBOR data item. They return TLC integers, booleans, strings, sequences, sets, records, functions, or existing model values.

The decoders accept these noncanonical forms:

- Integers, tags, and lengths with argument widths longer than necessary, within the supported value and input limits.
- Set elements, map keys, and tag 33000 pairs in any order.
- Maps with non-string keys, when TLC can represent and compare those keys.

Maps and tag 33000 functions are converted according to their domains. A function with domain `1..n` becomes a sequence, a function with a nonempty string domain becomes a record, and another function remains a function. Re-encoding a decoded value uses the encoder's representation and ordering, not necessarily the original bytes.

The decoders reject these inputs:

- Duplicate set elements or duplicate function keys, including map keys. Duplicates are determined by TLC value comparison, not by byte equality. For example, `01` and `18 01` both encode the integer `1`.
- Set elements or function keys that TLC cannot compare with one another.
- Integers outside `-2147483648..2147483647`.
- Floating-point numbers, CBOR byte strings, `null`, `undefined`, and other unsupported simple values.
- Indefinite-length items, unsupported tags, and malformed CBOR, including truncated input.
- Tag 39 without a text string, tag 258 without an array, or tag 33000 without an array of two-element arrays.
- Invalid UTF-8 text.
- Model value names that are not known to the current TLC model.
- Any bytes after the first data item.

Decode errors identify a zero-based byte offset. An invalid `FromCBOR` argument, such as a non-sequence or an integer outside `0..255`, produces an argument error instead.

## Round trips and limits

For a value `v` accepted by the encoder, the round-trip equation is:

```tla
FromCBOR(ToCBOR(v)) = v
```

The equation requires TLC to be able to compare the elements of each set in `v`, and the domain elements of each function in `v`. TLC cannot compare `1` with `"a"`. `ToCBOR` can encode `{1, "a"}`, but `FromCBOR` rejects those bytes. The same comparability restriction applies to file round trips.

After a successful `CBORSerialize(f, v)`, decoding the unchanged file with `CBORDeserialize(f)` returns `v`, subject to those round-trip requirements. The serialization operator itself returns `TRUE`, not the encoded value.

Sets and function domains must be finite, and TLC must be able to enumerate them. Function arguments and values must themselves be encodable. Operators and other unsupported TLC values cannot be encoded. Integers are limited to TLC's signed 32-bit range.

Strings must contain valid Unicode. The encoder rejects an unpaired UTF-16 surrogate rather than silently replacing it. The decoder rejects malformed UTF-8 rather than inserting a replacement character.

Tag 39 decoding reuses model values already known to TLC, for example values declared in the model's configuration file. It never creates a model value from an input name. Unknown names are errors.

There is no fixed nesting limit. Deep values can exhaust the JVM stack and cause `StackOverflowError` during encoding or decoding. A larger JVM `-Xss` setting can allow deeper values but does not remove that limit.
