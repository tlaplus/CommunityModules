package tlc2.overrides;
/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

import tlc2.value.IValue;
import tlc2.value.impl.*;

import java.util.Arrays;

public class Json {

	// Convert sets and sequences to JSON arrays.
	// Convert records to JSON objects.
	// E.g.
	// {1, 2, 3} -> "[1, 2, 3]"
	// <<"a", "b", "c">> -> "[\"a\", \"b\", \"c\"]"
	// (p1 :> 0 @@ p2 :> 0 @@ p3 :> 0) -> "{\"p1\": 0, \"p2\": 0, \"p3\": 0)
	@TLAPlusOperator(identifier = "ToJsonObject", module = "Json", warn = false)
	public static StringValue ToJsonObject(final IValue v) {
		final StringBuffer buf = new StringBuffer();
		toJsonObject(buf, v);
		return new StringValue(buf.toString());
	}

	private static boolean toJsonObject(final StringBuffer buf, final IValue v) {
		// Most Value implementations have either `toFcnRcd` or `toSetEnum` implemented, so we use them for the actual
		// conversions.
		if (v instanceof FcnRcdValue) {
			final FcnRcdValue frv = (FcnRcdValue) v;
			TupleValue tv = (TupleValue) toTuple(frv);
			if (tv != null) {
				tv.normalize();
				serializeJsonArray(buf, tv.elems);
			} else {
				final String[] keys = Arrays.stream(frv.domain).map(Json::toKey).toArray(size -> new String[size]);
				serializeJsonObject(buf, keys, frv.values);
			}
		} else if (v instanceof SetEnumValue) {
			// SetEnumValue does not have a `toFcnRcd` implemented.
			SetEnumValue sev = (SetEnumValue) v;
			sev.normalize();
			serializeJsonArray(buf, sev.elems.toArray());
		} else if (v instanceof RecordValue) {
			final Value vv = (Value) v;
			toJsonObject(buf, vv.toFcnRcd());
		} else if (v instanceof TupleValue) {
			final Value vv = (Value) v;
			toJsonObject(buf, vv.toFcnRcd());
		} else if (v instanceof SetOfFcnsValue) {
			final SetOfFcnsValue sofv = (SetOfFcnsValue) v;
			toJsonObject(buf, sofv.toSetEnum());
		} else if (v instanceof SetOfRcdsValue) {
			final SetOfRcdsValue sorv = (SetOfRcdsValue) v;
			toJsonObject(buf, sorv.toSetEnum());
		} else if (v instanceof SetOfTuplesValue) {
			final SetOfTuplesValue sotv = (SetOfTuplesValue) v;
			toJsonObject(buf, sotv.toSetEnum());
		} else if (v instanceof SubsetValue) {
			final SubsetValue sv = (SubsetValue) v;
			toJsonObject(buf, sv.toSetEnum());
		} else if (v instanceof IntervalValue) {
			final IntervalValue iv = (IntervalValue) v;
			toJsonObject(buf, iv.toSetEnum());
		} else {
			// XXX What to throw?
		}

		return false;
	}

	// From FcnRcdValue.java
	private static Value toTuple(final FcnRcdValue frv) {
		if (frv.intv != null) {
			if (frv.intv.low == 1) {
				return frv.toTuple();
			} else {
				return null;
			}
		}
		for (int i = 0; i < frv.domain.length; i++) {
		  if (!(frv.domain[i] instanceof IntValue)) {
			return null;
		  }
		}
		frv.normalize();
		for (int i = 0; i < frv.domain.length; i++) {
		  if (((IntValue)frv.domain[i]).val != (i+1)) {
			return null;
		  }
		}
		return frv.toTuple();
	}

	private static void toJson(final StringBuffer buf, final IValue v) {
		if (!toJsonObject(buf, v)) {
			if (v instanceof BoolValue) {
				final BoolValue bv = (BoolValue) v;
				buf.append(bv.val ? "true" : "false");
			} else if (v instanceof IntValue) {
				final IntValue iv = (IntValue) v;
				buf.append(iv.val);
			} else if (v instanceof ModelValue) {
				final ModelValue mv = (ModelValue) v;
				buf.append("\"");
				buf.append(mv.val);
				buf.append("\"");
			} else if (v instanceof StringValue) {
				final StringValue sv = (StringValue) v;
				buf.append("\"");
				buf.append(sv.val);
				buf.append("\"");
			} else {
				// XXX what to throw?
			}
		}
	}

	private static String toKey(final IValue v) {
		if (v instanceof BoolValue) {
			final BoolValue bv = (BoolValue) v;
			return bv.val ? "true" : "false";
		} else if (v instanceof IntValue) {
			final IntValue iv = (IntValue) v;
			return Integer.toString(iv.val);
		} else if (v instanceof ModelValue) {
			final ModelValue mv = (ModelValue) v;
			return mv.val.toString();
		} else if (v instanceof StringValue) {
			final StringValue sv = (StringValue) v;
			return sv.val.toString();
		}

		// XXX what to throw?
		return null;
	}

	private static void serializeJsonObject(final StringBuffer buf, final String[] keys, final Value[] vs) {
		buf.append("{");
		for (int i = 0; i < keys.length; i++) {
			if (i > 0) {
				buf.append(", ");
			}
			buf.append("\"");
			buf.append(keys[i]);
			buf.append("\": ");
			toJson(buf, vs[i]);
		}
		buf.append("}");
	}

	private static void serializeJsonArray(final StringBuffer buf, final Value[] vs) {
		buf.append("[");
		for (int i = 0; i < vs.length; i++) {
			if (i > 0) {
				buf.append(", ");
			}
			toJson(buf, vs[i]);
		}
		buf.append("]");
	}
}
