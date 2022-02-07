/*******************************************************************************
 * Copyright (c) 2022 Inria. All rights reserved. 
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
 *   Stephan Merz - initial implementation
 ******************************************************************************/
package tlc2.overrides;

import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.OpValue;
import tlc2.value.impl.Value;

public final class BagsExt {

	private BagsExt() {
		// no-instantiation!
	}

	@TLAPlusOperator(identifier = "FoldBag", module = "BagsExt", warn = false)
	public static Value foldBag(final OpValue op, final Value base, final Value bag) {
		// Can assume type of OpValue because tla2sany.semantic.Generator.java will
		// make sure that the first parameter is a binary operator.

		FcnRcdValue bfcn = (FcnRcdValue) bag.toFcnRcd();
		if (bfcn == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "third", "FoldBag", "bag", Values.ppr(bag.toString()) });
		}

		final Value[] domain = bfcn.getDomainAsValues();
		final Value[] values = bfcn.values;
		final Value acc[] = new Value[2];
		acc[0] = base;

		for (int i = 0; i < domain.length; i++) {
			acc[1] = domain[i];
			if (!(values[i] instanceof IntValue) || (((IntValue) values[i]).val <= 0)) {
					throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE,
							new String[] { "FoldBag", "an element of Nat", Values.ppr(values[i].toString()) + " (in: "
									+ Values.ppr(domain[i].toString()) + ":>" + Values.ppr(values[i].toString()) + ")" });
			}
			for (int j = 0; j < ((IntValue) values[i]).val; j++) {
				acc[0] = op.apply(acc, EvalControl.Clear);
			}
		}

		return acc[0];
	}
}
