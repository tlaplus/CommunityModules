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
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;

public class Json {

	// (p1 :> 0 @@ p2 :> 0 @@ p3 :> 0)
	// ->
	// "{\"p1\":0, \"p2\":0, \"p3\":0}"
	public static final StringValue ToJsonObject(final IValue v) {
		final StringBuffer buf = new StringBuffer();
		buf.append("{");
		
		if (v instanceof FcnRcdValue) {
			final FcnRcdValue r = (FcnRcdValue) v;
			for (int i = 0; i < r.domain.length; i++) {
				buf.append("\"");
				buf.append(r.domain[i]);
				buf.append("\"");
				
				buf.append(":");
				buf.append(r.values[i]);
				if (i < r.domain.length - 1) {
					buf.append(",");
				}
			}
		} else if (v instanceof TupleValue) {
			final TupleValue t = (TupleValue) v;
			for (int i = 0; i < t.elems.length; i++) {
				buf.append("\"");
				buf.append(IntValue.gen(i + 1));
				buf.append("\"");
				
				buf.append(":");
				buf.append(t.elems[i]);
				if (i < t.elems.length - 1) {
					buf.append(",");
				}
			}
		}
		
		buf.append("}");
		return new StringValue(buf.toString());
	}
}
