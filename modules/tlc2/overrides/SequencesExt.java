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
import java.util.Arrays;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;

public final class SequencesExt {
	
	private SequencesExt() {
		// no-instantiation!
	}
	
	@TLAPlusOperator(identifier = "IsInjective", module = "SequencesExt", warn = false)
	public static BoolValue IsInjective(final Value val) {
		if (val instanceof TupleValue) {
			return isInjectiveNonDestructive(((TupleValue) val).elems);
		} else {
			final Value conv = val.toTuple();
			if (conv == null) {
				throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
						new String[] { "IsInjective", "sequence", Values.ppr(val.toString()) });
			}
			return isInjectiveDestructive(((TupleValue) conv).elems);
		}
	}
	
	// O(n log n) runtime and O(1) space.
	private static BoolValue isInjectiveDestructive(final Value[] values) {
		Arrays.sort(values);
		for (int i = 1; i < values.length; i++) {
			if (values[i-1].equals(values[i])) {
				return BoolValue.ValFalse;
			}
		}
		return BoolValue.ValTrue;
	}

	// Assume small arrays s.t. the naive approach with O(n^2) runtime but O(1)
	// space is good enough. Sorting values in-place is a no-go because it
	// would modify the TLA+ tuple. Elements can be any sub-type of Value, not
	// just IntValue.
	private static BoolValue isInjectiveNonDestructive(final Value[] values) {
		for (int i = 0; i < values.length; i++) {
			for (int j = i + 1; j < values.length; j++) {
				if (values[i].equals(values[j])) {
					return BoolValue.ValFalse;
				}
			}
		}
		return BoolValue.ValTrue;
	}
}
