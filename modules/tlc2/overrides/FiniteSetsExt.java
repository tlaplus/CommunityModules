/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
package tlc2.overrides;

import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.value.IBoolValue;
import tlc2.value.Values;
import tlc2.value.impl.Applicable;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.EnumerableValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.KSubsetValue;
import tlc2.value.impl.OpValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SubsetValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;

public class FiniteSetsExt {
	
	private FiniteSetsExt() {
		// no-instantiation!
	}

	@TLAPlusOperator(identifier = "Quantify", module = "FiniteSetsExt", warn = false)
	public static Value quantify(final Value set, final Value pred) {
		if (!(set instanceof EnumerableValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "Quantify", "set", Values.ppr(set.toString()) });
		}
		if (!(pred instanceof Applicable)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "second", "Quantify", "boolean-valued operator", Values.ppr(pred.toString()) });
		}
		
		
		int size = 0;
		final Applicable test = (Applicable) pred;
		final ValueEnumeration enumSet = ((SetEnumValue) set.toSetEnum()).elements();
        Value elem;
        final Value[] args = new Value[1];
		while ((elem = enumSet.nextElement()) != null) {
			args[0] = elem;
			Value val = test.apply(args, EvalControl.Clear);
			if (val instanceof IBoolValue) {
				if (((BoolValue) val).val) {
					size++;
				}
			} else {
				throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "Quantify",
						"boolean-valued operator", Values.ppr(test.toString()) });
			}
		}

		assert 0 <= size && size <= set.size();
		return IntValue.gen(size);
	}
	
	@TLAPlusOperator(identifier = "kSubset", module = "FiniteSetsExt", warn = false)
	public static Value kSubset(final Value kv, final Value s) {
		final SetEnumValue set = (SetEnumValue) s.toSetEnum();
		if (set == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "second", "kSubset", "set", Values.ppr(s.toString()) });
		}
		if (!(kv instanceof IntValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "kSubset", "natural number", Values.ppr(kv.toString()) });
		}
		final int k = ((IntValue) kv).val;
		
		if (k < 0 || set.size() < k) {
			return SetEnumValue.EmptySet;
		}
		if (k == 0) {
			return new SubsetValue(SetEnumValue.EmptySet);
		}
		return new KSubsetValue(k, set, set.cm);
	}

	@TLAPlusOperator(identifier = "FoldSet", module = "FiniteSetsExt", warn = false)
	public static Value foldSet(final OpValue op, final Value base, final Enumerable set) {

		final Value[] args = new Value[2];
		args[1] = base;
		
		final ValueEnumeration ve = set.elements();

		Value v = null;
		while ((v = ve.nextElement()) != null) {
			args[0] = v;
			args[1] = op.apply(args, EvalControl.Clear);
		}
		
		return args[1];
	}
}
