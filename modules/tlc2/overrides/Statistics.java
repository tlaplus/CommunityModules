/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved.
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

import java.util.Arrays;

import org.apache.commons.math3.stat.inference.ChiSquareTest;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;

public class Statistics {

	@TLAPlusOperator(identifier = "ChiSquare", module = "Statistics", warn = false)
	public static Value chiSquare(Value expected, Value actual, final Value alpha) {
		expected = expected.normalize().toFcnRcd();
		if (!(expected instanceof FcnRcdValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "ChiSquare", "function", Values.ppr(expected.toString()) });
		}
		actual = actual.normalize().toFcnRcd();
		if (!(actual instanceof FcnRcdValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "second", "ChiSquare", "function", Values.ppr(actual.toString()) });
		}
		if (!(alpha instanceof StringValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "third", "ChiSquare",
					"StringValue representing a double in (0, .5]", Values.ppr(alpha.toString()) });
		}

		final double[] exp = Arrays.asList(((FcnRcdValue) expected).values).stream().map(v -> (IntValue) v)
				.mapToDouble(i -> Double.valueOf(i.val)).toArray();

		final long[] act = Arrays.asList(((FcnRcdValue) actual).values).stream().map(v -> (IntValue) v)
				.mapToLong(i -> Long.valueOf(i.val)).toArray();

		final double a = Double.valueOf(((StringValue) alpha).val.toString());

		final ChiSquareTest chiSquareTest = new ChiSquareTest();
		if (chiSquareTest.chiSquareTest(exp, act, a)) {
			return BoolValue.ValFalse;
		}
		return BoolValue.ValTrue;
	}
}
