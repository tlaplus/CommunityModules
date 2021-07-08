/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.Value;

public class Combinatorics {

	@TLAPlusOperator(identifier = "factorial", module = "Combinatorics", warn = false)
	public static Value fact(final Value n) {
		if (!(n instanceof IntValue) || ((IntValue) n).val < 0) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "factorial", "natural number", Values.ppr(n.toString()) });
		}
		try {
			return IntValue.gen(tlc2.util.Combinatorics.fact(((IntValue) n).val).intValueExact());
		} catch (ArithmeticException e) {
			throw new EvalException(EC.TLC_MODULE_OVERFLOW, n.toString());
		}
	}

	@TLAPlusOperator(identifier = "choose", module = "Combinatorics", warn = false)
	public static Value chse(final Value n, final Value k) {
		if (!(n instanceof IntValue) || ((IntValue) n).val < 0) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "choose", "natural number", Values.ppr(n.toString()) });
		}
		if (!(k instanceof IntValue) || ((IntValue) k).val < 0) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "second", "choose", "natural number", Values.ppr(k.toString()) });
		}
		try {
			return IntValue
					.gen(Math.toIntExact(tlc2.util.Combinatorics.choose(((IntValue) n).val, ((IntValue) k).val)));
		} catch (ArithmeticException e) {
			throw new EvalException(EC.TLC_MODULE_OVERFLOW, n + "choose" + k);
		}
	}
}
