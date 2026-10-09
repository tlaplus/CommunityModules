/*******************************************************************************
 * Copyright (c) 2026 Younes Akhouayri. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Younes Akhouayri - initial API and implementation
 ******************************************************************************/
package tlc2.overrides;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.EnumerableValue;
import tlc2.value.impl.FcnLambdaValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.Assert.TLCRuntimeException;
import util.UniqueString;

/**
 * Module overrides for CBOR.tla: encode a finite TLA+ value as CBOR (RFC 8949), as a sequence of bytes or
 * in a file, and decode it back. CBOR.tla documents the encoding; this class is its only implementation.
 *
 * <p>There is no intermediate data model. {@link Encoder} walks TLC values and writes bytes, and
 * {@link Decoder} reads bytes and builds TLC values. The four operators are thin shells around them. Both
 * decide how a function is written by one rule, {@link #shape(Value[])}, so the form the encoder writes and
 * the class the decoder builds cannot drift apart. The class depends only on TLC and the JDK.
 *
 * <p>Every error this class raises is an {@link EvalException}, never a Java exception that TLC would wrap
 * as error 2154. A wrong argument type uses the CommunityModules argument codes; errors about a value or a
 * file use {@link EC#GENERAL}, whose message TLC prints verbatim. An error that TLC raises itself while the
 * encoder enumerates a value, such as {x \in Nat : x < 3}, still arrives wrapped.
 */
public final class CBOR {

	private CBOR() {
	}

	// Major types, RFC 8949 section 3.1.
	private static final int UNSIGNED = 0, NEGATIVE = 1, BYTES = 2, TEXT = 3, ARRAY = 4, MAP = 5, TAG = 6, SIMPLE = 7;

	/** IANA tag 39, "Identifier", around a model value's name. */
	private static final int TAG_MODEL_VALUE = 39;
	/** IANA tag 258, "Mathematical finite set", around the array of a set's elements. */
	private static final int TAG_SET = 258;
	/**
	 * IANA tag 33000, "TLA+ function as an array of [argument, value] pairs", registered for this module on
	 * 2026-10-08, around the [x, f[x]] pairs of a function that is neither a sequence nor a record. CBOR.tla
	 * is the only other place that names it.
	 */
	private static final int TAG_FUNCTION = 33000;

	/**
	 * The deepest nesting of data items that the decoder reads, which bounds its recursion, so hostile input
	 * is an error instead of a stack overflow. The encoder refuses to write deeper, so it writes nothing the
	 * decoder rejects for its depth. A tag is a data item: a set takes two levels and the pairs of tag 33000
	 * three.
	 */
	private static final int MAX_DEPTH = 512;

	/**
	 * Guards file reads and writes, not encoding, so that a read in one worker never sees half of
	 * another worker's write to the same file.
	 */
	private static final Object FILES = new Object();

	/** How a function is written. TLC equates functions across Java classes, so only the domain decides. */
	private enum Shape {
		/** DOMAIN f = 1..n for some n >= 0: an array. Includes the empty function and the empty record. */
		SEQUENCE,
		/** A non-empty set of strings: a map keyed by text. */
		RECORD,
		/** Anything else: tag 33000 around [x, f[x]] pairs. */
		PAIRS
	}

	private static Shape shape(final Value[] domain) {
		final boolean[] seen = new boolean[domain.length + 1];
		int indices = 0;
		boolean strings = domain.length > 0;
		for (final Value d : domain) {
			strings &= d instanceof StringValue;
			if (d instanceof IntValue) {
				final int i = ((IntValue) d).val;
				if (1 <= i && i <= domain.length && !seen[i]) {
					seen[i] = true;
					indices++;
				}
			}
		}
		return indices == domain.length ? Shape.SEQUENCE : strings ? Shape.RECORD : Shape.PAIRS;
	}

	@TLAPlusOperator(identifier = "ToCBOR", module = "CBOR", warn = false)
	public static TupleValue toCBOR(final Value value) {
		final byte[] bytes = Encoder.encode(value, "ToCBOR", 1);
		final Value[] elems = new Value[bytes.length];
		for (int i = 0; i < elems.length; i++) {
			elems[i] = IntValue.gen(bytes[i] & 0xff);
		}
		return new TupleValue(elems);
	}

	/** Accepts any value that TLC converts to a sequence, such as [i \in 1..n |-> ...]. */
	@TLAPlusOperator(identifier = "FromCBOR", module = "CBOR", warn = false)
	public static Value fromCBOR(final Value bytes) {
		final Value seq = bytes.toTuple();
		if (seq == null) {
			throw notBytes(bytes);
		}
		final Value[] elems = ((TupleValue) seq).elems;
		final byte[] in = new byte[elems.length];
		for (int i = 0; i < in.length; i++) {
			final int b = elems[i] instanceof IntValue ? ((IntValue) elems[i]).val : -1;
			if (b < 0 || b > 255) {
				throw notBytes(bytes);
			}
			in[i] = (byte) b;
		}
		return new Decoder(in, "FromCBOR").document();
	}

	private static EvalException notBytes(final Value v) {
		return new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
				new String[] { "FromCBOR", "sequence of integers in 0..255", Values.ppr(v.toString()) });
	}

	/**
	 * Encodes the whole value before it touches the file, so a value it refuses leaves an existing file
	 * as it was.
	 */
	@TLAPlusOperator(identifier = "CBORSerialize", module = "CBOR", warn = false)
	public static BoolValue serialize(final Value absoluteFilename, final Value value) {
		if (!(absoluteFilename instanceof StringValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "CBORSerialize", "string", Values.ppr(absoluteFilename.toString()) });
		}
		final String file = ((StringValue) absoluteFilename).val.toString();
		final byte[] bytes = Encoder.encode(value, "CBORSerialize", 1);
		synchronized (FILES) {
			try {
				final Path path = Paths.get(file);
				final Path parent = path.toAbsolutePath().getParent();
				if (parent != null) {
					Files.createDirectories(parent);
				}
				Files.write(path, bytes);
			} catch (IOException | InvalidPathException e) {
				throw new EvalException(EC.GENERAL, "CBORSerialize could not write " + file + ": " + e + ".");
			}
		}
		return BoolValue.ValTrue;
	}

	/**
	 * With the default minLevel, a zero-arity definition such as Log == CBORDeserialize("log.cbor") is
	 * constant-level, so TLC reads the file once, before it starts checking.
	 */
	@TLAPlusOperator(identifier = "CBORDeserialize", module = "CBOR", warn = false)
	public static Value deserialize(final Value absoluteFilename) {
		if (!(absoluteFilename instanceof StringValue)) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "CBORDeserialize", "string", Values.ppr(absoluteFilename.toString()) });
		}
		final String file = ((StringValue) absoluteFilename).val.toString();
		final byte[] bytes;
		synchronized (FILES) {
			try {
				bytes = Files.readAllBytes(Paths.get(file));
			} catch (NoSuchFileException e) {
				throw new EvalException(EC.GENERAL,
						"CBORDeserialize could not read " + file + ": the file does not exist.");
			} catch (IOException | InvalidPathException e) {
				throw new EvalException(EC.GENERAL, "CBORDeserialize could not read " + file + ": " + e + ".");
			}
		}
		return new Decoder(bytes, "CBORDeserialize could not read " + file).document();
	}

	/**
	 * Writes the one encoding of a TLC value. Values that TLC considers equal produce identical bytes,
	 * whatever their Java class and whatever order TLC interned their strings in, so the encoder sorts by
	 * encoded bytes and never consults TLC's normalized order. It never calls normalize() either, so it
	 * mutates nothing that other workers read.
	 *
	 * <p>Set elements and the keys of maps and pairs are the sort keys. Each is encoded once into its own
	 * array, sorted, and copied into the parent. Map and pair values stream straight into the output.
	 */
	private static final class Encoder {

		private final ByteArrayOutputStream out = new ByteArrayOutputStream();
		private final String operator;

		private Encoder(final String operator) {
			this.operator = operator;
		}

		static byte[] encode(final Value v, final String operator, final int depth) {
			final Encoder e = new Encoder(operator);
			e.value(v, depth);
			return e.out.toByteArray();
		}

		/** depth is the level of the data item that v becomes, counted as the decoder counts it. */
		private void value(final Value v, final int depth) {
			level(depth);
			if (v instanceof IntValue) {
				integer(((IntValue) v).val);
			} else if (v instanceof BoolValue) {
				out.write(((BoolValue) v).val ? 0xf5 : 0xf4);
			} else if (v instanceof StringValue) {
				text(((StringValue) v).val.toString());
			} else if (v instanceof ModelValue) {
				head(TAG, TAG_MODEL_VALUE);
				level(depth + 1);
				text(((ModelValue) v).val.toString());
			} else if (v instanceof TupleValue) {
				array(((TupleValue) v).elems, depth);
			} else if (v instanceof RecordValue) {
				// Not toFcnRcd(), which normalizes the record in place.
				final RecordValue r = (RecordValue) v;
				final Value[] names = new Value[r.names.length];
				for (int i = 0; i < names.length; i++) {
					names[i] = new StringValue(r.names[i]);
				}
				function(names, r.values, depth);
			} else if (v instanceof FcnRcdValue) {
				final FcnRcdValue f = (FcnRcdValue) v;
				function(f.getDomainAsValues(), f.values, depth);
			} else if (v instanceof FcnLambdaValue) {
				// The domain, not the function: TLC prints a function's body as its source location.
				final Value domain = ((FcnLambdaValue) v).getDomain();
				if (!domain.isFinite()) {
					throw cannotEncode("a function with the infinite domain", domain);
				}
				value(v.toFcnRcd(), depth);
			} else if (v instanceof EnumerableValue) {
				if (!v.isFinite()) {
					throw cannotEncode("an infinite set", v);
				}
				set(((SetEnumValue) v.toSetEnum()).elems.toArray(), depth);
			} else {
				throw cannotEncode(v.getKindString(), v);
			}
		}

		private void level(final int depth) {
			if (depth > MAX_DEPTH) {
				throw new EvalException(EC.GENERAL,
						operator + " cannot encode a value nested more than " + MAX_DEPTH + " CBOR data items deep.");
			}
		}

		private void function(final Value[] domain, final Value[] values, final int depth) {
			final Shape shape = shape(domain);
			if (shape == Shape.SEQUENCE) {
				final Value[] elems = new Value[domain.length];
				for (int i = 0; i < domain.length; i++) {
					elems[((IntValue) domain[i]).val - 1] = values[i];
				}
				array(elems, depth);
				return;
			}
			// A pair is an array inside the array inside the tag.
			final int entry = shape == Shape.RECORD ? depth + 1 : depth + 3;
			final byte[][] keys = encodeEach(domain, entry);
			final Integer[] order = new Integer[keys.length];
			for (int i = 0; i < order.length; i++) {
				order[i] = i;
			}
			Arrays.sort(order, (i, j) -> Arrays.compareUnsigned(keys[i], keys[j]));
			if (shape == Shape.RECORD) {
				head(MAP, keys.length);
			} else {
				head(TAG, TAG_FUNCTION);
				head(ARRAY, keys.length);
			}
			for (final int i : order) {
				if (shape == Shape.PAIRS) {
					head(ARRAY, 2);
				}
				write(keys[i]);
				value(values[i], entry);
			}
		}

		private void array(final Value[] elems, final int depth) {
			head(ARRAY, elems.length);
			for (final Value e : elems) {
				value(e, depth + 1);
			}
		}

		/**
		 * An unnormalized set may hold an element twice, possibly in two Java classes. Equal elements have
		 * equal encodings, so dropping equal neighbours after sorting removes exactly TLC's duplicates.
		 */
		private void set(final Value[] elems, final int depth) {
			level(depth + 1);
			final byte[][] items = encodeEach(elems, depth + 2);
			Arrays.sort(items, Arrays::compareUnsigned);
			int n = 0;
			for (final byte[] item : items) {
				if (n == 0 || !Arrays.equals(item, items[n - 1])) {
					items[n++] = item;
				}
			}
			head(TAG, TAG_SET);
			head(ARRAY, n);
			for (int i = 0; i < n; i++) {
				write(items[i]);
			}
		}

		private byte[][] encodeEach(final Value[] values, final int depth) {
			final byte[][] encoded = new byte[values.length][];
			for (int i = 0; i < values.length; i++) {
				encoded[i] = encode(values[i], operator, depth);
			}
			return encoded;
		}

		private void integer(final int n) {
			if (n >= 0) {
				head(UNSIGNED, n);
			} else {
				head(NEGATIVE, -1 - n);
			}
		}

		/**
		 * Uses a CharsetEncoder, which reports errors, because String.getBytes turns an unpaired UTF-16
		 * surrogate (SubSeq can cut one out of a string) into '?' without notice.
		 */
		private void text(final String s) {
			final ByteBuffer utf8;
			try {
				utf8 = StandardCharsets.UTF_8.newEncoder().encode(CharBuffer.wrap(s));
			} catch (CharacterCodingException e) {
				throw new EvalException(EC.GENERAL,
						operator + " cannot encode a string that contains an unpaired UTF-16 surrogate.");
			}
			head(TEXT, utf8.remaining());
			out.write(utf8.array(), utf8.arrayOffset() + utf8.position(), utf8.remaining());
		}

		/**
		 * The initial byte and the shortest argument. Every argument fits in four bytes: integers are
		 * 32-bit, so -1 - n never exceeds Integer.MAX_VALUE, and lengths are Java array sizes.
		 */
		private void head(final int major, final int n) {
			final int ib = major << 5;
			if (n < 24) {
				out.write(ib | n);
			} else if (n <= 0xff) {
				out.write(ib | 24);
				out.write(n);
			} else if (n <= 0xffff) {
				out.write(ib | 25);
				out.write(n >>> 8);
				out.write(n);
			} else {
				out.write(ib | 26);
				out.write(n >>> 24);
				out.write(n >>> 16);
				out.write(n >>> 8);
				out.write(n);
			}
		}

		private void write(final byte[] bytes) {
			out.write(bytes, 0, bytes.length);
		}

		private EvalException cannotEncode(final String kind, final Value v) {
			return new EvalException(EC.GENERAL,
					operator + " cannot encode " + kind + ":\n" + Values.ppr(v.toString()));
		}
	}

	/**
	 * Reads one CBOR data item into a TLC value. Liberal about form, strict about meaning: it accepts set
	 * elements, map keys and pairs in any order, integers and lengths in any width, and maps with keys that
	 * are not strings. Encoders in other languages differ on exactly these by default, and none of them
	 * changes the TLA+ value. It rejects every item whose TLA+ meaning is missing, out of TLC's range, or
	 * ambiguous, and names the source and the byte offset of the item.
	 *
	 * <p>It never creates a model value. ModelValue.make at run time leaves ModelValue.mvs stale, and TLC
	 * reads model values back from its disk queues by index into mvs.
	 */
	private static final class Decoder {

		private final byte[] in;
		private final String prefix;
		private int pos;
		/** The bytes that the unread items of the enclosing arrays and maps need, at one byte an item. */
		private int owed;
		private Map<String, ModelValue> modelValues;

		Decoder(final byte[] in, final String prefix) {
			this.in = in;
			this.prefix = prefix;
		}

		Value document() {
			final Value v = item(1);
			if (pos != in.length) {
				throw error(pos, "there are bytes after the first CBOR data item");
			}
			return v;
		}

		private Value item(final int depth) {
			final int start = pos;
			final int ib = initial(depth);
			final int major = ib >>> 5;
			if (major == SIMPLE) {
				return simple(start, ib & 0x1f);
			}
			final long arg = argument(start, major, ib & 0x1f);
			switch (major) {
			case UNSIGNED:
			case NEGATIVE:
				return integer(start, arg, major == NEGATIVE);
			case BYTES:
				throw error(start, "a byte string has no TLA+ counterpart");
			case TEXT:
				return new StringValue(text(start, arg));
			case ARRAY:
				return new TupleValue(items(count(start, arg, 1), depth + 1));
			case MAP:
				final int n = count(start, arg, 2);
				final Value[] keys = new Value[n], values = new Value[n];
				owed += 2 * n;
				for (int i = 0; i < n; i++) {
					keys[i] = member(depth + 1);
					values[i] = member(depth + 1);
				}
				return function(start, keys, values);
			default:
				return tagged(start, arg, depth);
			}
		}

		private Value simple(final int start, final int ai) {
			switch (ai) {
			case 20:
				return BoolValue.ValFalse;
			case 21:
				return BoolValue.ValTrue;
			case 22:
				throw error(start, "null has no TLA+ counterpart");
			case 23:
				throw error(start, "undefined has no TLA+ counterpart");
			case 25:
			case 26:
			case 27:
				throw error(start, "a floating-point number has no TLA+ counterpart");
			case 28:
			case 29:
			case 30:
			case 31:
				throw notWellFormed(start);
			default:
				throw error(start, "a simple value has no TLA+ counterpart");
			}
		}

		private Value tagged(final int start, final long tag, final int depth) {
			if (tag == TAG_MODEL_VALUE) {
				final int at = pos;
				final int ib = initial(depth + 1);
				if (ib >>> 5 != TEXT) {
					throw error(start, "tag 39 must enclose a text string");
				}
				return modelValue(start, text(at, argument(at, TEXT, ib & 0x1f)));
			}
			if (tag == TAG_SET) {
				return set(start, items(arrayHead(start, depth + 1, "tag 258 must enclose an array"), depth + 2));
			}
			if (tag == TAG_FUNCTION) {
				final String complaint = "tag " + TAG_FUNCTION + " must enclose an array of [key, value] arrays";
				final int n = arrayHead(start, depth + 1, complaint);
				final Value[] keys = new Value[n], values = new Value[n];
				owed += n;
				for (int i = 0; i < n; i++) {
					owed--;
					if (arrayHead(start, depth + 2, complaint) != 2) {
						throw error(start, complaint);
					}
					owed += 2;
					keys[i] = member(depth + 3);
					values[i] = member(depth + 3);
				}
				return function(start, keys, values);
			}
			throw error(start, "tag " + Long.toUnsignedString(tag) + " has no TLA+ counterpart");
		}

		/** The length of the array that must follow the tag at start. */
		private int arrayHead(final int start, final int depth, final String complaint) {
			final int at = pos;
			final int ib = initial(depth);
			if (ib >>> 5 != ARRAY) {
				throw error(start, complaint);
			}
			return count(at, argument(at, ARRAY, ib & 0x1f), 1);
		}

		private Value function(final int start, final Value[] keys, final Value[] values) {
			final Integer[] order = distinct(start, keys, "key");
			final int n = keys.length;
			switch (shape(keys)) {
			case SEQUENCE:
				final Value[] elems = new Value[n];
				for (int i = 0; i < n; i++) {
					elems[((IntValue) keys[i]).val - 1] = values[i];
				}
				return new TupleValue(elems);
			case RECORD:
				final UniqueString[] names = new UniqueString[n];
				final Value[] fields = new Value[n];
				for (int i = 0; i < n; i++) {
					names[i] = ((StringValue) keys[order[i]]).val;
					fields[i] = values[order[i]];
				}
				return new RecordValue(names, fields, true);
			default:
				final Value[] domain = new Value[n], range = new Value[n];
				for (int i = 0; i < n; i++) {
					domain[i] = keys[order[i]];
					range[i] = values[order[i]];
				}
				return new FcnRcdValue(domain, range, true);
			}
		}

		private Value set(final int start, final Value[] elems) {
			final Integer[] order = distinct(start, elems, "element");
			final Value[] sorted = new Value[elems.length];
			for (int i = 0; i < sorted.length; i++) {
				sorted[i] = elems[order[i]];
			}
			return new SetEnumValue(sorted, true);
		}

		/**
		 * Sorts indices into TLC's order, which lets the caller build normalized values. Equality is TLC's,
		 * not bytewise: 01 and 18 01 are the same element. TLC's compareTo fails on values it cannot
		 * compare (1 and "a"); reporting that here is clearer than a failure at first use in the spec.
		 */
		private Integer[] distinct(final int start, final Value[] items, final String what) {
			final Integer[] order = new Integer[items.length];
			for (int i = 0; i < order.length; i++) {
				order[i] = i;
			}
			Arrays.sort(order, (i, j) -> {
				try {
					return items[i].compareTo(items[j]);
				} catch (TLCRuntimeException e) {
					throw error(start, "TLC cannot compare the " + what + "s " + ppr(items[Math.min(i, j)]) + " and "
							+ ppr(items[Math.max(i, j)]));
				}
			});
			for (int k = 1; k < order.length; k++) {
				if (items[order[k - 1]].compareTo(items[order[k]]) == 0) {
					throw error(start, "the " + what + " " + ppr(items[order[k]]) + " occurs twice");
				}
			}
			return order;
		}

		/** arg is an unsigned 64-bit number. */
		private Value integer(final int start, final long arg, final boolean negative) {
			if (arg < 0 || arg > Integer.MAX_VALUE) {
				final BigInteger n = new BigInteger(Long.toUnsignedString(arg));
				throw error(start, "the integer " + (negative ? n.not() : n)
						+ " is outside TLC's range -2147483648..2147483647");
			}
			return IntValue.gen(negative ? (int) ~arg : (int) arg);
		}

		/** A strict decoder: malformed UTF-8 is an error, never U+FFFD. */
		private String text(final int start, final long length) {
			final int n = count(start, length, 1);
			final String s;
			try {
				s = StandardCharsets.UTF_8.newDecoder().decode(ByteBuffer.wrap(in, pos, n)).toString();
			} catch (CharacterCodingException e) {
				throw error(start, "a text string is not valid UTF-8");
			}
			pos += n;
			return s;
		}

		private ModelValue modelValue(final int start, final String name) {
			if (modelValues == null) {
				modelValues = new HashMap<>();
				for (final ModelValue mv : ModelValue.mvs) {
					modelValues.put(mv.val.toString(), mv);
				}
			}
			final ModelValue mv = modelValues.get(name);
			if (mv == null) {
				throw new EvalException(EC.GENERAL,
						message(start, "the model value " + name + " is not defined in the model")
						+ " Declare it in the .cfg or create it with TLCExt!TLCModelValue(\"" + name + "\").");
			}
			return mv;
		}

		private Value[] items(final int n, final int depth) {
			final Value[] items = new Value[n];
			owed += n;
			for (int i = 0; i < n; i++) {
				items[i] = member(depth);
			}
			return items;
		}

		/** The next of the items that an array or a map has added to owed. */
		private Value member(final int depth) {
			owed--;
			return item(depth);
		}

		private int initial(final int depth) {
			if (pos == in.length) {
				throw error(pos, "the input ends inside a CBOR data item");
			}
			if (depth > MAX_DEPTH) {
				throw error(pos, "data items are nested more than " + MAX_DEPTH + " deep");
			}
			return in[pos++] & 0xff;
		}

		private long argument(final int start, final int major, final int ai) {
			if (ai < 24) {
				return ai;
			}
			if (ai == 31 && BYTES <= major && major <= MAP) {
				throw error(start, "indefinite-length items are not supported");
			}
			if (ai > 27) {
				throw notWellFormed(start);
			}
			final int size = 1 << (ai - 24);
			if (in.length - pos < size) {
				throw error(start, "the input ends inside a CBOR data item");
			}
			long arg = 0;
			for (int i = 0; i < size; i++) {
				arg = arg << 8 | in[pos++] & 0xff;
			}
			return arg;
		}

		/**
		 * Checked before anything is allocated. The bytes owed to the enclosing arrays and maps are not
		 * available. Otherwise each of 512 nested arrays could claim the rest of the input, and the decoder
		 * would allocate 512 times the input's size instead of an amount in proportion to it.
		 */
		private int count(final int start, final long n, final int minBytesPerItem) {
			if (n < 0 || n > (in.length - pos - owed) / minBytesPerItem) {
				throw error(start, "the input ends inside a CBOR data item");
			}
			return (int) n;
		}

		private EvalException notWellFormed(final int start) {
			return error(start, String.format("the initial byte 0x%02x is not well-formed", in[start] & 0xff));
		}

		private EvalException error(final int offset, final String problem) {
			return new EvalException(EC.GENERAL, message(offset, problem));
		}

		private String message(final int offset, final String problem) {
			return prefix + ": " + problem + " at byte " + offset + ".";
		}

		private static String ppr(final Value v) {
			return Values.ppr(v.toString());
		}
	}
}
