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

import org.apache.commons.lang3.StringUtils;

import tla2sany.semantic.ExprOrOpArgNode;
import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.Values;
import tlc2.value.impl.Applicable;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.OpValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;
import tlc2.value.impl.ValueVec;

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

	
	 public String longestCommonPrefix(String[] strs) {
		    if (strs.length == 0) return "";
		    String prefix = strs[0];
		    for (int i = 1; i < strs.length; i++)
		        while (strs[i].indexOf(prefix) != 0) {
		            prefix = prefix.substring(0, prefix.length() - 1);
		            if (prefix.isEmpty()) return "";
		        }        
		    return prefix;
		}
	/*
	 */
		@TLAPlusOperator(identifier = "FoldFunction", module = "Functions", warn = false)
		public static Value foldFunction(final OpValue op, final Value base, final Applicable fun) {
			return foldFunctionOnSet(op, base, fun, (Enumerable) fun.getDomain());
		}

		@TLAPlusOperator(identifier = "FoldFunctionOnSet", module = "Functions", warn = false)
		public static Value foldFunctionOnSet(final OpValue op, final Value base, final Applicable fun, final Enumerable subdomain) {
			
			final Value[] args = new Value[2];
			args[1] = base;

			final ValueEnumeration ve = subdomain.elements();

			Value v = null;
			while ((v = ve.nextElement()) != null) {
				args[0] = fun.select(v);
				args[1] = op.apply(args, EvalControl.Clear);
			}
			
			return args[1];
		}

	@TLAPlusOperator(identifier = "LongestCommonPrefix", module = "SequencesExt", warn = false)
	public static Value longestCommonPrefix(final Value val) {
		final SetEnumValue set = (SetEnumValue) val.toSetEnum();
		if (set == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "LongestCommonPrefix", "non-empty set", Values.ppr(val.toString()) });
		}
		
		// Never iterate over non-normalized values. Convenient side-effect:
		// Normalization moves the shortest element to the front: {"ab", "a"} becomes
		// {"a", "ab"}. This guards against OutOfBoundsExceptions later when other is
		// shorter than prefix.
		set.normalize();
		
		final ValueVec elems = set.elems;
		if (set.elems.isEmpty()) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "LongestCommonPrefix", "non-empty set", Values.ppr(val.toString()) });
		}
		
		try {
			final Value shortest = elems.elementAt(0);
			if (shortest instanceof StringValue) {
				return longestCommonPrefix((StringValue) shortest, elems);
			}
			Value[] prefix = ((TupleValue) shortest.toTuple()).elems;
			int upper = prefix.length;
			
			for (int i = 1; i < elems.size(); i++) {
				Value[] other = ((TupleValue) elems.elementAt(i).toTuple()).elems;
				for (int idx = 0; idx < upper; idx++) {
					if (!prefix[idx].equals(other[idx])) {
						upper = idx;
						if (upper == 0) {
							return TupleValue.EmptyTuple;
						}
					}
				}
			}
			if (upper == 0) {
				return TupleValue.EmptyTuple;
			}
			final Value[] res = new Value[upper];
			System.arraycopy(prefix, 0, res, 0, upper);
			return new TupleValue(res);
		} catch (ClassCastException | NullPointerException e) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR, new String[] { "LongestCommonPrefix",
					"sequence", Values.ppr(val.toString()) });
		}
	}
	
	private static Value longestCommonPrefix(final StringValue first, final ValueVec elems) {
		String prefix = first.val.toString();
		int upper = prefix.length();
		
		for (int i = 1; i < elems.size(); i++) {
			String other = ((StringValue) elems.elementAt(i)).val.toString();
			for (int idx = 0; idx < upper; idx++) {
				if (prefix.charAt(idx) != other.charAt(idx)) {
					upper = idx;
					if (upper == 0) {
						return new StringValue("");
					}
				}
			}
		}
		if (upper == 0) {
			return new StringValue("");
		}
		return new StringValue(prefix.substring(0, upper));
	}
	
	@TLAPlusOperator(identifier = "FoldSeq", module = "SequencesExt", warn = false)
	public static Value foldSeq(final OpValue op, final Value base, final TupleValue tv) {
		return foldLeft(op, base, tv);
	}

	@TLAPlusOperator(identifier = "FoldLeft", module = "SequencesExt", warn = false)
	public static Value foldLeft(final OpValue op, final Value base, final Value val) {

		final TupleValue tv = (TupleValue) val.toTuple();
		if (tv == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "FoldLeft", "sequence", Values.ppr(val.toString()) });
		}

		final Value[] args = new Value[2];
		args[0] = base;

		final Value[] elems = tv.elems;
		for (int i = 0; i < elems.length; i++) {
			args[1] = elems[i];
			args[0] = op.apply(args, EvalControl.Clear);
		}

		return args[0];
	}

	@TLAPlusOperator(identifier = "FoldRight", module = "SequencesExt", warn = false)
	public static Value foldRight(final OpValue op, final Value val, final Value base) {

		final TupleValue tv = (TupleValue) val.toTuple();
		if (tv == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "FoldRight", "sequence", Values.ppr(val.toString()) });
		}

		final Value[] args = new Value[2];
		args[1] = base;

		final Value[] elems = tv.elems;
		for (int i = elems.length - 1; i >= 0; i--) {
			args[0] = elems[i];
			args[1] = op.apply(args, EvalControl.Clear);
		}

		return args[1];
	}
	
	@Evaluation(definition = "ReplaceFirstSubSeq", module = "SequencesExt", warn = false, silent = true)
	public static Value replaceFirstSubSeq(final Tool tool, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final int control, final CostModel cm) {
		final IValue r = tool.eval(args[0], c, s0, s1, control, cm);
		final IValue s = tool.eval(args[1], c, s0, s1, control, cm);
		final IValue t = tool.eval(args[2], c, s0, s1, control, cm);
		
		if (r instanceof StringValue && s instanceof StringValue && t instanceof StringValue) {
			final String st = ((StringValue) t).getVal().toString();
			final String ss = ((StringValue) s).getVal().toString();
			final String sr = ((StringValue) r).getVal().toString();
			
			return new StringValue(StringUtils.replaceOnce(st, ss, sr));
		}
		
		return null; // Non-string functions handled by pure TLA+ definition of operator.
	}

	@Evaluation(definition = "ReplaceAllSubSeqs", module = "SequencesExt", warn = false, silent = true)
	public static Value replaceAllSubSeq(final Tool tool, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final int control, final CostModel cm) {
		final IValue r = tool.eval(args[0], c, s0, s1, control, cm);
		final IValue s = tool.eval(args[1], c, s0, s1, control, cm);
		final IValue t = tool.eval(args[2], c, s0, s1, control, cm);
		
		if (r instanceof StringValue && s instanceof StringValue && t instanceof StringValue) {
			final String st = ((StringValue) t).getVal().toString();
			final String ss = ((StringValue) s).getVal().toString();
			final String sr = ((StringValue) r).getVal().toString();
			
			return new StringValue(StringUtils.replace(st, ss, sr));
		}
		
		return null; // Non-string functions handled by pure TLA+ definition of operator.
	}
}
