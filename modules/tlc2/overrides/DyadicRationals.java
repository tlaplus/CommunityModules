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

import org.apache.commons.math3.util.ArithmeticUtils;

import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.UniqueString;

public class DyadicRationals {

	private static final StringValue DEN = new StringValue("den");
	private static final StringValue NUM = new StringValue("num");
	
	/*
	LOCAL Reduce(p) ==
    LET gcd == GCD(p.num, p.den)
    IN  IF gcd = 1 THEN p
        ELSE Rational(p.num \div gcd, p.den \div gcd)

	 */
	@TLAPlusOperator(identifier = "Reduce", module = "DyadicRationals", warn = false)
	public static Value reduce(final Value val) {
		if (!(val instanceof RecordValue)) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "Half", "record", Values.ppr(val.toString()) });
		}
		
		final RecordValue r = (RecordValue) val;
		r.normalize();
		
		final IntValue d = (IntValue) r.apply(DEN, EvalControl.Clear);
		final IntValue n = (IntValue) r.apply(NUM, EvalControl.Clear);

		final int gcd = ArithmeticUtils.gcd(n.val, d.val);
		if (gcd == 1) {
			return r;
		}
		
		final UniqueString[] names = new UniqueString[2];
		names[0] = DEN.val;
		names[1] = NUM.val;
		
		final Value[] values = new Value[2];	
		values[0] = IntValue.gen(d.val / gcd);
		values[1] = IntValue.gen(n.val / gcd);
		
		return new RecordValue(names, values, false);
	}
}
