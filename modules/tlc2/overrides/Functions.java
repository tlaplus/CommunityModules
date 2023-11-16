/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 * Copyright (c) 2023, Oracle and/or its affiliates.
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

import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.FunctionValue;
import tlc2.value.impl.OpValue;
import tlc2.value.impl.SetOfRcdsValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;

public final class Functions {
	
	private Functions() {
		// no-instantiation!
	}
	
	@TLAPlusOperator(identifier = "IsInjective", module = "Functions", warn = false)
	public static BoolValue IsInjective(final Value val) {
		if (val instanceof TupleValue) {
			return isInjectiveNonDestructive(((TupleValue) val).elems);
		} else if (val instanceof FcnRcdValue && ((FcnRcdValue) val).intv != null
				&& ((FcnRcdValue) val).intv.low == 1) {
			// Input a FcnRcdValue whose toTuple representation can non be mutated.
			return isInjectiveNonDestructive(((FcnRcdValue) val).values);
		} else {
			final Value conv = val.toTuple();
			if (conv != null) {
				// toTuple creates a new instance that we can safely mutate!
				return isInjectiveDestructive(((TupleValue) conv).elems);
			}
			if (val instanceof SetOfRcdsValue) {
				// Input e.g. [a: 1, b: 2]
				return isInjectiveNonDestructive(((SetOfRcdsValue) val).values);
			} else if (val instanceof FcnRcdValue) {
				// Input e.g. [a |-> 1, b |-> 2]
				return isInjectiveNonDestructive(((FcnRcdValue) val).values);
			}
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "IsInjective", "function", Values.ppr(val.toString()) });
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
	
	@TLAPlusOperator(identifier = "AntiFunction", module = "Functions", warn = false)
	public static Value antiFunction(final Value f) {
		// AntiFunction(f) == [t \in Range(f) |-> CHOOSE s \in DOMAIN f : t \in Range(f) => f[s] = t]
		final FcnRcdValue frc = (FcnRcdValue) f.normalize().toFcnRcd();
		if (frc == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "AntiFunction", "functions", Values.ppr(f.toString()) });
		}
		final Value[] range;
		if (frc.intv != null) {
			range = frc.getDomainAsValues();
		} else {
			final Value[] values = frc.getDomainAsValues();
			range = Arrays.copyOf(values, values.length);
		}
		final Value[] domain = Arrays.copyOf(frc.values, frc.values.length);
		return new FcnRcdValue(domain, range, false).normalize();
	}

	@TLAPlusOperator(identifier = "FoldFunction", module = "Functions", warn = false)
	public static Value foldFunction(final OpValue op, final Value base, final Value fun) {
		// Can assume type of OpValue because tla2sany.semantic.Generator.java will
		// make sure that the first parameter is a binary operator.
		
		if (!(fun instanceof FunctionValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "third", "FoldFunction", "function", Values.ppr(fun.toString()) });
		}
		return foldFunctionOnSet(op, base, fun, ((FunctionValue) fun).getDomain());
	}

	@TLAPlusOperator(identifier = "FoldFunctionOnSet", module = "Functions", warn = false)
	public static Value foldFunctionOnSet(final OpValue op, final Value base, final Value v3, final Value v4) {
		// Can assume type of OpValue because tla2sany.semantic.Generator.java will
		// make sure that the first parameter is a binary operator.

		if (!(v3 instanceof FunctionValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "third", "FoldFunctionOnSet", "function", Values.ppr(v3.toString()) });
		}
		final FunctionValue fun = (FunctionValue) v3;
		if (!(v4 instanceof Enumerable)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "fourth", "FoldFunctionOnSet", "set", Values.ppr(v4.toString()) });
		}
		final Enumerable subdomain = (Enumerable) v4;
		
		// FoldFunction base is second operand.
		final Value[] args = new Value[2];
		args[1] = base;

		final ValueEnumeration ve = subdomain.elements();

		Value v;
		while ((v = ve.nextElement()) != null) {
			args[0] = fun.apply(v, EvalControl.Clear);
			args[1] = op.eval(args, EvalControl.Clear);
		}
		
		return args[1];
	}
}
