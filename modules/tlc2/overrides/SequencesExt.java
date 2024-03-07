package tlc2.overrides;
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

import java.util.ArrayList;

import org.apache.commons.lang3.StringUtils;

import tla2sany.semantic.ExprOrOpArgNode;
import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IBoolValue;
import tlc2.value.IValue;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.OpValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
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

	@TLAPlusOperator(identifier = "SetToSeqs", module = "SequencesExt", warn = false)
	public static Value SetToSeqs(final Value s) {		
        SetEnumValue s1 = (SetEnumValue) s.toSetEnum();
        if (s1 == null)
        {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "SetToSeqs",
                    "a finite set", Values.ppr(s.toString()) });
        }
        s1.normalize();
        ValueVec elems = s1.elems;
        int len = elems.size();
        if (len == 0)
        {
        	Value[] elems1 = { FcnRcdValue.EmptyFcn };
            return new SetEnumValue(elems1, true);
        }

        int factorial = 1;
        Value [] domain = new Value[len];
        int[] idxArray = new int[len];
        boolean[] inUse = new boolean[len];
        for (int i = 0; i < len; i++)
        {
            domain[i] = elems.elementAt(i);
            idxArray[i] = i;
            inUse[i] = true;
            factorial = factorial * (i + 1);
        }

        ValueVec fcns = new ValueVec(factorial);
        _done: while (true)
        {
        	Value [] vals = new Value[len];
            for (int i = 0; i < len; i++)
            {
                vals[i] = domain[idxArray[i]];
            }
            // Except for this line, this method is a copy of tlc2.module.TLC#Permutations.
            fcns.addElement(new TupleValue(vals));
            int i;
            for (i = len - 1; i >= 0; i--)
            {
                boolean found = false;
                for (int j = idxArray[i] + 1; j < len; j++)
                {
                    if (!inUse[j])
                    {
                        inUse[j] = true;
                        inUse[idxArray[i]] = false;
                        idxArray[i] = j;
                        found = true;
                        break;
                    }
                }
                if (found) {
                    break;
                }
                if (i == 0) {
                    break _done;
                }
                inUse[idxArray[i]] = false;
            }
            for (int j = i + 1; j < len; j++)
            {
                for (int k = 0; k < len; k++)
                {
                    if (!inUse[k])
                    {
                        inUse[k] = true;
                        idxArray[j] = k;
                        break;
                    }
                }
            }
        }
        return new SetEnumValue(fcns, false);
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
	public static Value foldSeq(final OpValue op, final Value base, final Value tv) {
		return Functions.foldFunction(op, base, tv);
	}

	@TLAPlusOperator(identifier = "FoldLeft", module = "SequencesExt", warn = false)
	public static Value foldLeft(final OpValue op, final Value base, final Value val) {
		// Can assume type of OpValue because tla2sany.semantic.Generator.java will
		// make sure that the first parameter is a binary operator.
		
		final TupleValue tv = (TupleValue) val.toTuple();
		if (tv == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "third", "FoldLeft", "sequence", Values.ppr(val.toString()) });
		}

		// FoldLeft base is left (first) operand.
		final Value[] args = new Value[2];
		args[0] = base;

		final Value[] elems = tv.elems;
		for (int i = 0; i < elems.length; i++) {
			args[1] = elems[i];
			args[0] = op.eval(args, EvalControl.Clear);
		}

		return args[0];
	}

	@TLAPlusOperator(identifier = "FoldRight", module = "SequencesExt", warn = false)
	public static Value foldRight(final OpValue op, final Value val, final Value base) {
		// Can assume type of OpValue because tla2sany.semantic.Generator.java will
		// make sure that the first parameter is a binary operator.
		
		final TupleValue tv = (TupleValue) val.toTuple();
		if (tv == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "second", "FoldRight", "sequence", Values.ppr(val.toString()) });
		}

		// FoldRight base is right (second) operand.
		final Value[] args = new Value[2];
		args[1] = base;

		final Value[] elems = tv.elems;
		for (int i = elems.length - 1; i >= 0; i--) {
			args[0] = elems[i];
			args[1] = op.eval(args, EvalControl.Clear);
		}

		return args[1];
	}

	@TLAPlusOperator(identifier = "FoldLeftDomain", module = "SequencesExt", warn = false)
	public static Value foldLeftDomain(final OpValue op, final Value base, final Value val) {
		final TupleValue tv = (TupleValue) val.toTuple();
		if (tv == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "third", "FoldLeftDomain", "sequence", Values.ppr(val.toString()) });
		}

		final Value[] args = new Value[2];
		args[0] = base;

		for (int i = 0; i < tv.size(); i++) {
			args[1] = IntValue.gen(i+1);
			args[0] = op.eval(args, EvalControl.Clear);
		}

		return args[0];
	}

	@TLAPlusOperator(identifier = "FoldRightDomain", module = "SequencesExt", warn = false)
	public static Value foldRightDomain(final OpValue op, final Value val, final Value base) {
		final TupleValue tv = (TupleValue) val.toTuple();
		if (tv == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "second", "FoldRightDomain", "sequence", Values.ppr(val.toString()) });
		}

		final Value[] args = new Value[2];
		args[1] = base;

		for (int i = tv.size() - 1; i >= 0; i--) {
			args[0] = IntValue.gen(i+1);
			args[1] = op.eval(args, EvalControl.Clear);
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
			
			if(ss.equals("")) { return new StringValue(sr+st); }
			
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
			
			if(ss.equals("")) {
				StringBuilder result = new StringBuilder(sr);
				for(int i=0;i<st.length();i++) {
					if(i != 0) { result.append(sr); }
					result.append(st.charAt(i));
				}
				return new StringValue(result.toString());
			}
			
			return new StringValue(StringUtils.replace(st, ss, sr));
		}
		
		return null; // Non-string functions handled by pure TLA+ definition of operator.
	}

	@TLAPlusOperator(identifier = "IsPrefix", module = "SequencesExt", warn = false)
	public static Value isPrefix(final Value v1, final Value v2) {
		if (v1 instanceof StringValue && v2 instanceof StringValue) {
			final StringValue s1 = (StringValue) v1;
			final StringValue s2 = (StringValue) v2;
			if (s2.getVal().toString().startsWith(s1.getVal().toString())) {
				return BoolValue.ValTrue;
			}
			return BoolValue.ValFalse;
		}

		// No need to normalize s and t because TupleValuels are normalized by construction.
		final TupleValue s = (TupleValue) v1.toTuple();
		final TupleValue t = (TupleValue) v2.toTuple();

		if (s.size() <= t.size()) {
			for (int i = 0 ; i < s.size(); i++) {
				final Value vs = s.elems[i];
				final Value vt = t.elems[i];
				if (!vs.equals(vt)) {
					return BoolValue.ValFalse;
				}
			}
			return BoolValue.ValTrue;
		}
		return BoolValue.ValFalse;
	}

	@TLAPlusOperator(identifier = "SelectInSeq", module = "SequencesExt", warn = false)
	public static Value selectInSeq(final Value s, final OpValue test) {
		final TupleValue seq = (TupleValue) s.toTuple();
		if (seq == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "SelectInSeq", "sequence", Values.ppr(s.toString()) });
		}
		final int len = seq.size();
		final Value[] args = new Value[1];
		for (int i = 0; i < len; i++) {
			args[0] = seq.elems[i];
			final Value val = test.eval(args, EvalControl.Clear);
			if (!(val instanceof IBoolValue)) {
				throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "third", "SelectInSeq",
						"boolean-valued operator", Values.ppr(test.toString()) });
			}
			if (((BoolValue) val).val) {
				return IntValue.gen(i + 1);
			}
		}
		return IntValue.ValZero;
	}

	@TLAPlusOperator(identifier = "SelectInSubSeq", module = "SequencesExt", warn = false)
	public static Value SelectInSubSeq(final Value s, final Value f, final Value t, final OpValue test) {
		final TupleValue seq = (TupleValue) s.toTuple();
		if (seq == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "SelectInSubSeq", "sequence", Values.ppr(s.toString()) });
		}
		if (!(f instanceof IntValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "second", "SelectInSubSeq", "natural", Values.ppr(f.toString()) });
		}
		if (!(t instanceof IntValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "third", "SelectInSubSeq", "natural", Values.ppr(t.toString()) });
		}

		int from = ((IntValue) f).val;
		final int to = ((IntValue) t).val;
		
		if (from > to) {
			return IntValue.ValZero;
		}
		if (from < 1 || from > seq.size()) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN,
					new String[] { "second", "SelectInSubSeq", "first", Values.ppr(s.toString()), Values.ppr(f.toString()) });
		}
		if (to < 1 || to > seq.size()) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN,
					new String[] { "third", "SelectInSubSeq", "first", Values.ppr(s.toString()), Values.ppr(t.toString()) });
		}

		final Value[] args = new Value[1];
		for (; from <= to; from++) {
			args[0] = seq.elems[from - 1];
			final Value val = test.eval(args, EvalControl.Clear);
			if (!(val instanceof IBoolValue)) {
				throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "fourth", "SelectInSubSeq",
						"boolean-valued operator", Values.ppr(test.toString()) });
			}
			if (((BoolValue) val).val) {
				return IntValue.gen(from);
			}
		}
		return IntValue.ValZero;
	}
	
	@TLAPlusOperator(identifier = "SelectLastInSeq", module = "SequencesExt", warn = false)
	public static Value selectLastInSeq(final Value s, final OpValue test) {
		final TupleValue seq = (TupleValue) s.toTuple();
		if (seq == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "SelectLastInSeq", "sequence", Values.ppr(s.toString()) });
		}
		int i = seq.size() - 1;
		final Value[] args = new Value[1];
		for (; i >= 0; i--) {
			args[0] = seq.elems[i];
			final Value val = test.eval(args, EvalControl.Clear);
			if (!(val instanceof IBoolValue)) {
				throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "third", "SelectLastInSeq",
						"boolean-valued function", Values.ppr(test.toString()) });
			}
			if (((BoolValue) val).val) {
				return IntValue.gen(i + 1);
			}
		}
		return IntValue.ValZero;
	}

	@TLAPlusOperator(identifier = "SelectLastInSubSeq", module = "SequencesExt", warn = false)
	public static Value SelectLastInSubSeq(final Value s, final Value f, final Value t, final OpValue test) {
		final TupleValue seq = (TupleValue) s.toTuple();
		if (seq == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "SelectLastInSubSeq", "sequence", Values.ppr(s.toString()) });
		}
		if (!(f instanceof IntValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "second", "SelectLastInSubSeq", "natural", Values.ppr(f.toString()) });
		}
		if (!(t instanceof IntValue)) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "third", "SelectLastInSubSeq", "natural", Values.ppr(t.toString()) });
		}

		final int from = ((IntValue) f).val;
		int to = ((IntValue) t).val;
		
		if (from > to) {
			return IntValue.ValZero;
		}	
		if (from < 1 || from > seq.size()) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN,
					new String[] { "second", "SelectLastInSubSeq", "first", Values.ppr(s.toString()), Values.ppr(f.toString()) });
		}
		if (to < 1 || to > seq.size()) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN,
					new String[] { "third", "SelectLastInSubSeq", "first", Values.ppr(s.toString()), Values.ppr(t.toString()) });
		}

		final Value[] args = new Value[1];
		for (; to >= from; to--) {
			args[0] = seq.elems[to - 1];
			final Value val = test.eval(args, EvalControl.Clear);
			if (!(val instanceof IBoolValue)) {
				throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "fourth", "SelectLastInSubSeq",
						"boolean-valued function", Values.ppr(test.toString()) });
			}
			if (((BoolValue) val).val) {
				return IntValue.gen(to);
			}
		}
		return IntValue.ValZero;
	}
	
	@TLAPlusOperator(identifier = "RemoveFirst", module = "SequencesExt", warn = false)
	public static Value removeFirst(final Value s, final Value e) {
		final TupleValue seq = (TupleValue) s.toTuple();
		if (seq == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "RemoveFirst", "sequence", Values.ppr(s.toString()) });
		}

		final ArrayList<Value> val = new ArrayList<>(seq.elems.length);
		
		boolean found = false;
		for (int i = 0; i < seq.elems.length; i++) {
			if (!found && seq.elems[i].equals(e)) {
				found = true;
			} else {
				val.add(seq.elems[i]);
			}
		}
		
		return new TupleValue(val.toArray(Value[]::new));
	}
	
	@TLAPlusOperator(identifier = "RemoveFirstMatch", module = "SequencesExt", warn = false)
	public static Value removeFirstMatch(final Value s, final OpValue test) {
		final TupleValue seq = (TupleValue) s.toTuple();
		if (seq == null) {
			throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
					new String[] { "first", "RemoveFirstMatch", "sequence", Values.ppr(s.toString()) });
		}
		final Value[] args = new Value[1];

		final ArrayList<Value> val = new ArrayList<>(seq.elems.length);
		
		boolean found = false;
		for (int i = 0; i < seq.elems.length; i++) {
			if (!found) {
				args[0] = seq.elems[i];
				final Value bval = test.eval(args, EvalControl.Clear);
				if (!(bval instanceof IBoolValue)) {
					throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "RemoveFirstMatch",
							"boolean-valued function", Values.ppr(test.toString()) });
				}
				if (((BoolValue) bval).val) {
					found = true;
					continue;
				}
			}
			val.add(seq.elems[i]);
		}
		
		return new TupleValue(val.toArray(Value[]::new));
	}

	/*
	   Suffixes(s) ==
		  (**************************************************************************)
		  (* The set of suffixes of the sequence s, including the empty sequence.   *)
		  (**************************************************************************)
		  { SubSeq(s, l, Len(s)) : l \in 1..Len(s) } \cup {<<>>}
	 */
	@TLAPlusOperator(identifier = "Suffixes", module = "SequencesExt", warn = false)
	public static Value Suffixes(final Value s) {
		final TupleValue seq = (TupleValue) s.toTuple();
		if (seq == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "Suffixes", "sequence", Values.ppr(s.toString()) });
		}
		
		final Value[] vals = new Value[seq.elems.length + 1];
		
		// \cup {<<>>} 
		vals[0] = TupleValue.EmptyTuple;
		
		// Add the elements in reverse order to implicitly normalize the SetEnumValue.
		for (int i = seq.elems.length - 1; i >= 0; i--) {
			final Value[] suffix = new Value[seq.elems.length - i];
			System.arraycopy(seq.elems, i, suffix, 0, seq.elems.length - i);
			
			vals[seq.elems.length - i] = new TupleValue(suffix);
		}
		
		// Decided against calling "normalize" as a safeguard, even though "vals" will
		// be normalized. This is because "normalize," albeit performing a single pass
		// over "vals" for a normalized input, still compares elements, which can be
		// expensive: return new SetEnumValue(vals, false).normalize();
		return new SetEnumValue(vals, true);
	}

	/*
	 * AllSubSeqs(s) ==
	 *    { FoldFunction(Snoc, <<>>, [ i \in D |-> s[i] ]) : D \in SUBSET DOMAIN s }
	 */
	@TLAPlusOperator(identifier = "AllSubSeqs", module = "SequencesExt", warn = false)
	public static Value AllSubSeqs(final Value s) {
		final TupleValue seq = (TupleValue) s.toTuple();
		if (seq == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "AllSubSeqs", "sequence", Values.ppr(s.toString()) });
		}

		final int n = seq.elems.length;
		final Value[] vals = new Value[(int) Math.pow(2, n)];

		for (int i = 0; i < (1 << n); i++) {
			int k = 0;
			final Value[] subSeq = new Value[Long.bitCount(i)];
			for (int j = 0; j < n; j++) {
				if ((i & (1 << j)) != 0) {
					subSeq[k++] = seq.elems[j];
				}
			}
			vals[i] = new TupleValue(subSeq);
		}

		return new SetEnumValue(vals, false);
	}
}
