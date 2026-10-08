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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.Test;

/**
 * Checks the golden bytes in tests/CBORTests.tla against a second CBOR encoder. {@code ant test} runs it on
 * every operating system before TLC, and it needs JUnit alone.
 *
 * <p>The encoder below is a second implementation of the encoding table in modules/CBOR.tla that shares no
 * code with CBOR.java. CBORTests.tla states each golden as an ASSUME that calls Golden or SameBytes with the
 * golden's name and its bytes as a TLA+ sequence of hex literals ({@code <<\h82, \h61, ...>>}). TLC checks
 * that ToCBOR writes those bytes; this test checks that they are the bytes this encoder writes for the value
 * of the same name. It fails on a mismatch, printing the expected sequence, on a name it does not know, and
 * on a value it has that no ASSUME states.
 */
public class CBORGoldenTest {

	private static final int TAG_MODEL_VALUE = 39;
	private static final int TAG_SET = 258;
	private static final int TAG_FUNCTION = 33000;

	private static final Comparator<byte[]> BYTEWISE = Arrays::compareUnsigned;

	private static final class Mv {
		final String name;

		Mv(final String name) {
			this.name = name;
		}
	}

	private static final class Set {
		final Object[] elems;

		Set(final Object... elems) {
			this.elems = elems;
		}
	}

	/** A function given by its (x, f[x]) pairs. */
	private static final class Fn {
		final Object[][] pairs;

		Fn(final Object[]... pairs) {
			this.pairs = pairs;
		}
	}

	private static Object[] pair(final Object x, final Object fx) {
		return new Object[] { x, fx };
	}

	private static Map<String, Object> record(final Object... keysAndValues) {
		final Map<String, Object> r = new LinkedHashMap<>();
		for (int i = 0; i < keysAndValues.length; i += 2) {
			r.put((String) keysAndValues[i], keysAndValues[i + 1]);
		}
		return r;
	}

	private static byte[] head(final int major, final long n) {
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		if (n < 24) {
			out.write(major << 5 | (int) n);
			return out.toByteArray();
		}
		final int ai = n <= 0xFFL ? 24 : n <= 0xFFFFL ? 25 : n <= 0xFFFFFFFFL ? 26 : 27;
		final int width = 1 << ai - 24;
		out.write(major << 5 | ai);
		for (int i = width - 1; i >= 0; i--) {
			out.write((int) (n >>> 8 * i));
		}
		return out.toByteArray();
	}

	private static byte[] keyed(final List<Object[]> pairs, final boolean asMap) {
		final List<Object[]> entries = new ArrayList<>();
		for (final Object[] p : pairs) {
			entries.add(new Object[] { encode(p[0]), p[1] });
		}
		entries.sort((a, b) -> BYTEWISE.compare((byte[]) a[0], (byte[]) b[0]));
		for (int i = 1; i < entries.size(); i++) {
			assertTrue("duplicate key",
					BYTEWISE.compare((byte[]) entries.get(i - 1)[0], (byte[]) entries.get(i)[0]) != 0);
		}
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		if (asMap) {
			out.writeBytes(head(5, entries.size()));
		} else {
			out.writeBytes(head(6, TAG_FUNCTION));
			out.writeBytes(head(4, entries.size()));
		}
		for (final Object[] e : entries) {
			if (!asMap) {
				out.writeBytes(head(4, 2));
			}
			out.writeBytes((byte[]) e[0]);
			out.writeBytes(encode(e[1]));
		}
		return out.toByteArray();
	}

	private static byte[] function(final List<Object[]> pairs) {
		final List<Integer> intKeys = new ArrayList<>();
		boolean allStrings = true;
		for (final Object[] p : pairs) {
			if (p[0] instanceof Integer) {
				intKeys.add((Integer) p[0]);
			}
			allStrings &= p[0] instanceof String;
		}
		intKeys.sort(null);
		final List<Integer> oneToN = new ArrayList<>();
		for (int i = 1; i <= pairs.size(); i++) {
			oneToN.add(i);
		}
		if (intKeys.equals(oneToN)) {
			final Object[] values = new Object[pairs.size()];
			for (final Object[] p : pairs) {
				values[(Integer) p[0] - 1] = p[1];
			}
			return encode(Arrays.asList(values));
		}
		return keyed(pairs, allStrings);
	}

	private static byte[] encode(final Object v) {
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		if (v instanceof Boolean) {
			out.write((Boolean) v ? 0xf5 : 0xf4);
		} else if (v instanceof Integer) {
			final int n = (Integer) v;
			out.writeBytes(n >= 0 ? head(0, n) : head(1, -1L - n));
		} else if (v instanceof String) {
			final byte[] b = ((String) v).getBytes(StandardCharsets.UTF_8);
			out.writeBytes(head(3, b.length));
			out.writeBytes(b);
		} else if (v instanceof Mv) {
			out.writeBytes(head(6, TAG_MODEL_VALUE));
			out.writeBytes(encode(((Mv) v).name));
		} else if (v instanceof Set) {
			final TreeSet<byte[]> items = new TreeSet<>(BYTEWISE);
			for (final Object e : ((Set) v).elems) {
				items.add(encode(e));
			}
			out.writeBytes(head(6, TAG_SET));
			out.writeBytes(head(4, items.size()));
			items.forEach(out::writeBytes);
		} else if (v instanceof List) {
			final List<?> tuple = (List<?>) v;
			out.writeBytes(head(4, tuple.size()));
			for (final Object e : tuple) {
				out.writeBytes(encode(e));
			}
		} else if (v instanceof Map) {
			final List<Object[]> pairs = new ArrayList<>();
			((Map<?, ?>) v).forEach((k, fk) -> pairs.add(pair(k, fk)));
			out.writeBytes(function(pairs));
		} else if (v instanceof Fn) {
			out.writeBytes(function(Arrays.asList(((Fn) v).pairs)));
		} else {
			throw new AssertionError("no CBOR encoding for a " + v.getClass().getName()
					+ "; TLC integers are 32-bit, so a golden integer is an Integer");
		}
		return out.toByteArray();
	}

	private static final Mv MODEL_VALUE = new Mv("ModelValue");

	private static final Map<String, Object> S1 = record("x", 0, "y", new Set());
	private static final Map<String, Object> S2 = record("x", 1, "y", new Set(MODEL_VALUE));
	private static final Map<String, Object> LOCATION = record("beginLine", 5, "beginColumn", 9, "endLine", 5,
			"endColumn", 33, "module", "T");

	private static final Map<String, Object> GOLDEN = record(
			"int", List.of(0, 23, 24, 255, 256, 65535, 65536, 2147483647, -1, -24, -25, -256, -257, -2147483648),
			"bool", List.of(true, false),
			"string", List.of("", "a", "\u00fc", "\u65e5\u672c", "\uD83D\uDE00"),
			"modelvalue", MODEL_VALUE,
			"set", new Set(100, -1, 10),
			"set-strings", new Set("cbor-zz", "cbor-a", "cbor-aa"),
			"set-nested", new Set(new Set(), new Set(1), new Set(1, 2), new Set(2)),
			"set-wide", new Set(200, 24),
			"set-modelvalue", new Set(MODEL_VALUE, 1),
			"set-utf8", new Set("\u00e9", "zz"),
			"emptyset", new Set(),
			"interval", new Set(1, 2, 3),
			"seq", List.of("a", "b"),
			"empty", List.of(),
			"record", record("cborzz", 1, "cbora", 2, "cboraa", 3),
			"fcn-int", new Fn(pair(0, "x"), pair(1, "y")),
			"fcn-tuple", new Fn(pair(List.of(1, 2), 3), pair(List.of(2, 1), 3)),
			"fcn-set", new Fn(pair(new Set(), 0), pair(new Set(1), 1)),
			"fcn-record", new Fn(pair(record("a", 1), 1), pair(record("a", 2), 2)),
			"fcn-modelvalue", new Fn(pair(MODEL_VALUE, 0)),
			"fcn-mixed", new Fn(pair(MODEL_VALUE, 0), pair(1, 0)),
			"trace", record(
					"counterexample", record(
							"state", new Set(List.of(1, S1), List.of(2, S2)),
							"action", new Set(List.of(List.of(1, S1), record("name", "Next", "location", LOCATION),
									List.of(2, S2)))),
					"vars", new Set("x", "y")));

	private static final Pattern NAME = Pattern.compile("\\b(?:Golden|SameBytes)\\(\"([^\"]+)\"");
	private static final Pattern HEX_SEQUENCE = Pattern
			.compile("<<\\s*(\\\\h[0-9a-fA-F]{2}(?:\\s*,\\s*\\\\h[0-9a-fA-F]{2})*)\\s*>>");
	private static final Pattern HEX = Pattern.compile("\\\\h([0-9a-fA-F]{2})");
	private static final Pattern TOP_LEVEL_STATEMENT_BREAK = Pattern.compile("\n(?=\\S)");

	private static List<String> findAll(final Pattern p, final String s) {
		final List<String> found = new ArrayList<>();
		final Matcher m = p.matcher(s);
		while (m.find()) {
			found.add(m.group(1));
		}
		return found;
	}

	private static String tlaHexSequence(final byte[] data) {
		final List<String> lines = new ArrayList<>();
		for (int i = 0; i < data.length; i += 16) {
			final List<String> line = new ArrayList<>();
			for (int j = i; j < Math.min(i + 16, data.length); j++) {
				line.add(String.format("\\h%02x", data[j] & 0xff));
			}
			lines.add(String.join(", ", line));
		}
		return "<<" + String.join(",\n  ", lines) + ">>";
	}

	@Test
	public void goldensMatchASecondEncoder() throws IOException {
		final String text = Files.readString(Paths.get(System.getProperty("basepath", "tests"), "CBORTests.tla"),
				StandardCharsets.US_ASCII);
		final List<String> failures = new ArrayList<>();
		final HashSet<String> seen = new HashSet<>();
		int line = 1;
		for (final String stmt : TOP_LEVEL_STATEMENT_BREAK.split(text, -1)) {
			final int stmtLine = line;
			line += stmt.chars().filter(c -> c == '\n').count() + 1;
			final List<String> names = findAll(NAME, stmt);
			if (names.isEmpty()) {
				continue;
			}
			final List<String> literals = findAll(HEX_SEQUENCE, stmt);
			if (new HashSet<>(names).size() != 1 || literals.size() != 1) {
				failures.add(String.format(
						"line %d: expected one golden name and one hex sequence, found %s and %d sequences", stmtLine,
						names, literals.size()));
				continue;
			}
			final String name = names.get(0);
			if (!GOLDEN.containsKey(name)) {
				failures.add(String.format("line %d: no value for the golden '%s'", stmtLine, name));
				continue;
			}
			seen.add(name);
			final List<String> hex = findAll(HEX, literals.get(0));
			final byte[] stated = new byte[hex.size()];
			for (int i = 0; i < stated.length; i++) {
				stated[i] = (byte) Integer.parseInt(hex.get(i), 16);
			}
			final byte[] expected = encode(GOLDEN.get(name));
			if (Arrays.equals(stated, expected)) {
				System.out.printf("ok   %s (line %d)%n", name, stmtLine);
			} else {
				failures.add(String.format("line %d: the bytes of '%s' differ; this encoder writes\n%s", stmtLine,
						name, tlaHexSequence(expected)));
			}
		}
		for (final String name : GOLDEN.keySet()) {
			if (!seen.contains(name)) {
				failures.add(String.format("no ASSUME states the golden '%s'", name));
			}
		}
		assertEquals("", String.join("\n", failures));
	}
}
