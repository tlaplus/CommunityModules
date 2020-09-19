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
import tlc2.tool.coverage.CostModel;
import tlc2.value.IBoolValue;
import tlc2.value.Values;
import tlc2.value.impl.Applicable;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.EnumerableValue;
import tlc2.value.impl.IntValue;
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
					new String[] { "first", "FiniteSetsExt", "Quantify", Values.ppr(set.toString()) });
		}
		if (!(pred instanceof Applicable)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "second", "FiniteSetsExt", "Quantify", Values.ppr(pred.toString()) });
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
				throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "CardinalityOf",
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
					new String[] { "second", "FiniteSetsExt", "kSubset", Values.ppr(s.toString()) });
		}
		if (!(kv instanceof IntValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "FiniteSetsExt", "kSubset", Values.ppr(kv.toString()) });
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

	@SuppressWarnings("serial")
	public static class KSubsetValue extends SubsetValue {

		private final int k;

		public KSubsetValue(int k, Value set) {
			super(set);
			this.k = k;
		}

		public KSubsetValue(int k, Value set, CostModel cm) {
			super(set, cm);
			this.k = k;
		}

		@Override
		public ValueEnumeration elements() {
			// Remember k as a member and return SubsetValue's kElement enumerator here.
			return kElements(k);
		}
	}
}
