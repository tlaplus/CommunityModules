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

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;

public final class SequencesExt {
	
	private SequencesExt() {
		// no-instantiation!
	}
	
	/*
	 * Improve carbon footprint of SequencesExt!SetToSeq. Convert SetEnumValue to
	 * TupleValue (linear in the number of elements) instead of generating the set
	 * of *all* functions (n^n) and choosing one that's injective.
	 */
	@TLAPlusOperator(identifier = "SetToSeq", module = "SequencesExt", warn = false)
	public static Value SetToSeq(final Value val) {
		// TODO: This should eventually be replaced with SetEnumValue#toTupleValue.
		// I don't want to make CommunityModules depend on the most recent TLC nightly
		// build right now.
		final SetEnumValue setEnumValue = (SetEnumValue) val.toSetEnum().normalize();
		return new TupleValue(setEnumValue.elems.toArray());
	}

	/*
	 * Contains(s, e) == \E i \in 1..Len(s) : s[i] = e
	 */
	@TLAPlusOperator(identifier = "Contains", module = "SequencesExt", warn = false)
	public static Value Contains(final Value s, final Value e) {
		final TupleValue tv = (TupleValue) s.toTuple();
		if (tv == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "Contains", "sequence", Values.ppr(s.toString()) });
		}
		for (int i = 0; i < tv.elems.length; i++) {
			if (tv.elems[i].equals(e)) {
				return BoolValue.ValTrue;
			}
		}
		return BoolValue.ValFalse;
	}
}
