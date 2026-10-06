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
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;

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

/**
 * Module overrides for CBOR.tla: encode a finite TLA+ value as CBOR (RFC 8949), as a sequence of bytes or
 * in a file, and decode it back. CBOR.tla documents the encoding; this class is its only implementation.
 *
 * <p>There is no intermediate data model. {@link Encoder} walks TLC values and writes bytes, and the
 * operators are thin shells around it. Both directions decide how a function is written by one rule,
 * {@link #shape(Value[])}. The class depends only on TLC and the JDK.
 *
 * <p>Every error is an {@link EvalException}, never a Java exception that TLC would wrap as error 2154.
 * A wrong argument type uses the CommunityModules argument codes; errors about a value or a file use
 * {@link EC#GENERAL}, whose message TLC prints verbatim.
 */
public final class CBOR {

	private CBOR() {
	}

	// Major types, RFC 8949 section 3.1.
	private static final int UNSIGNED = 0, NEGATIVE = 1, TEXT = 3, ARRAY = 4, MAP = 5, TAG = 6;

	/** IANA tag 39, "Identifier", around a model value's name. */
	private static final int TAG_MODEL_VALUE = 39;
	/** IANA tag 258, "Mathematical finite set", around the array of a set's elements. */
	private static final int TAG_SET = 258;
	/**
	 * Around the [x, f[x]] pairs of a function that is neither a sequence nor a record. Not yet registered
	 * with IANA; 33000 lies in the First Come First Served range. CBOR.tla is the only other place that
	 * names it.
	 */
	private static final int TAG_FUNCTION = 33000;

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
		final byte[] bytes = Encoder.encode(value, "ToCBOR");
		final Value[] elems = new Value[bytes.length];
		for (int i = 0; i < elems.length; i++) {
			elems[i] = IntValue.gen(bytes[i] & 0xff);
		}
		return new TupleValue(elems);
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
		final byte[] bytes = Encoder.encode(value, "CBORSerialize");
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

		static byte[] encode(final Value v, final String operator) {
			final Encoder e = new Encoder(operator);
			e.value(v);
			return e.out.toByteArray();
		}

		private void value(final Value v) {
			if (v instanceof IntValue) {
				integer(((IntValue) v).val);
			} else if (v instanceof BoolValue) {
				out.write(((BoolValue) v).val ? 0xf5 : 0xf4);
			} else if (v instanceof StringValue) {
				text(((StringValue) v).val.toString());
			} else if (v instanceof ModelValue) {
				head(TAG, TAG_MODEL_VALUE);
				text(((ModelValue) v).val.toString());
			} else if (v instanceof TupleValue) {
				array(((TupleValue) v).elems);
			} else if (v instanceof RecordValue) {
				// Not toFcnRcd(), which normalizes the record in place.
				final RecordValue r = (RecordValue) v;
				final Value[] names = new Value[r.names.length];
				for (int i = 0; i < names.length; i++) {
					names[i] = new StringValue(r.names[i]);
				}
				function(names, r.values);
			} else if (v instanceof FcnRcdValue) {
				final FcnRcdValue f = (FcnRcdValue) v;
				function(f.getDomainAsValues(), f.values);
			} else if (v instanceof FcnLambdaValue) {
				// The domain, not the function: TLC prints a function's body as its source location.
				final Value domain = ((FcnLambdaValue) v).getDomain();
				if (!domain.isFinite()) {
					throw cannotEncode("a function with the infinite domain", domain);
				}
				value(v.toFcnRcd());
			} else if (v instanceof EnumerableValue) {
				if (!v.isFinite()) {
					throw cannotEncode("an infinite set", v);
				}
				set(((SetEnumValue) v.toSetEnum()).elems.toArray());
			} else {
				throw cannotEncode(v.getKindString(), v);
			}
		}

		private void function(final Value[] domain, final Value[] values) {
			final Shape shape = shape(domain);
			if (shape == Shape.SEQUENCE) {
				final Value[] elems = new Value[domain.length];
				for (int i = 0; i < domain.length; i++) {
					elems[((IntValue) domain[i]).val - 1] = values[i];
				}
				array(elems);
				return;
			}
			final byte[][] keys = encodeEach(domain);
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
				value(values[i]);
			}
		}

		private void array(final Value[] elems) {
			head(ARRAY, elems.length);
			for (final Value e : elems) {
				value(e);
			}
		}

		/**
		 * An unnormalized set may hold an element twice, possibly in two Java classes. Equal elements have
		 * equal encodings, so dropping equal neighbours after sorting removes exactly TLC's duplicates.
		 */
		private void set(final Value[] elems) {
			final byte[][] items = encodeEach(elems);
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

		private byte[][] encodeEach(final Value[] values) {
			final byte[][] encoded = new byte[values.length][];
			for (int i = 0; i < values.length; i++) {
				encoded[i] = encode(values[i], operator);
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
}
