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
package tlc2.overrides;

import java.io.IOException;
import java.util.Scanner;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.StringNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.ConcurrentTLCTrace;
import tlc2.tool.EvalException;
import tlc2.tool.ModelChecker;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.util.IdThread;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.Assert;

public class TLCExt {

	@Evaluation(definition = "AssertError", module = "TLCExt")
	public synchronized static Value assertError(final Tool tool, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
			final TLCState s1, final int control, final CostModel cm) {
		
		// Check expected err is a string.
		Assert.check(args[0] instanceof StringNode, "In computing AssertError, a non-string expression (" + args[0]
				+ ") was used as the err " + "of an AssertError(err, exp).");
		
		try {
			tool.eval(args[1], c, s0, s1, control, cm);
		} catch (EvalException e) {
			final StringValue err = (StringValue) tool.eval(args[0], c, s0);
			if (err.val.equals(e.getMessage())) {
				return BoolValue.ValTrue;
			}
		}
		return BoolValue.ValFalse;
	}
	
	private static final Scanner scanner = new Scanner(System.in);
	
	// This is likely only useful with a single worker, but let's synchronize anyway.
	@Evaluation(definition = "PickSuccessor", module = "TLCExt")
	public synchronized static Value pickSuccessor(final Tool tool, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
			final TLCState s1, final int control, final CostModel cm) {
		
		// Eval expression and only let user interactively pick successor states when it evaluates to FALSE.
		final Value guard = tool.eval(args[0], c, s0, s1, control, cm);
		if (!(guard instanceof BoolValue)) {
			Assert.fail("In evaluating TLCExt!PickSuccessor, a non-boolean expression (" + guard.getKindString()
					+ ") was used as the condition " + "of an IF.\n" + args[0]);
		}
		if (((BoolValue) guard).val) {
			return BoolValue.ValTrue;
		}
		
		// Find the (first) Action this pair of states belongs to. If more than one
		// Action match, we pick the first one. 
		// TODO: This is clumsy (we regenerate all next-states again) and incorrect if
		// two actions generate the same successor states. It's good enough for now
		// until the Action instance was passed down the call-stack.
		Action action = null;
		LOOP: for (Action act : tool.getActions()) {
			StateVec nextStates = tool.getNextStates(act, s0);
			if (nextStates.contains(s1)) {
				action = act;
				break LOOP;
			}
		}
		
		while (true) {
			// TODO Add more commands such as continue/resume to pick every successor,
			// randomly pick next N successors, terminate to stop state space exploration, ...
			MP.printMessage(EC.TLC_MODULE_OVERRIDE_STDOUT,
					String.format("Extend behavior of length %s with a \"%s\" step [%s]? (Yes/no/explored/states/diff):",
							s0.getLevel(), action.getName(), action));

			final String nextLine = scanner.nextLine();
			if (nextLine.trim().isEmpty() || nextLine.toLowerCase().startsWith("y")) {
				return BoolValue.ValTrue;
			} else if (nextLine.charAt(0) == 's') {
				MP.printMessage(EC.TLC_MODULE_OVERRIDE_STDOUT,
						String.format("%s\n~>\n%s", s0.toString().trim(), s1.toString().trim()));
			} else if (nextLine.charAt(0) == 'd') {
				MP.printMessage(EC.TLC_MODULE_OVERRIDE_STDOUT, s1.toString(s0));
			} else if (nextLine.charAt(0) == 'e') {
				try {
					((ModelChecker) TLCGlobals.mainChecker).theFPSet.put(s1.fingerPrint());
				} catch (IOException notExpectedToHappen) {
					notExpectedToHappen.printStackTrace();
				}
				return BoolValue.ValTrue;
			} else if (nextLine.charAt(0) == 'n') {
				return BoolValue.ValFalse;
			}
		}
	}

	@TLAPlusOperator(identifier = "Trace", module = "TLCExt", minLevel = 1)
	public synchronized static Value getTrace() throws IOException {
		final ModelChecker mc = (ModelChecker) TLCGlobals.mainChecker;
		final ConcurrentTLCTrace traceFile = mc.trace;

		final TLCState currentState = IdThread.getCurrentState();
		if (currentState == null) {
			return new TupleValue(new Value[0]);
		}
		
		final TLCStateInfo[] trace = traceFile.getTrace(currentState);
		final Value[] values = new Value[trace.length];
		for (int j = 0; j < trace.length; j++) {
			values[j] = new RecordValue(trace[j].state);
		}
		return new TupleValue(values);
	}
}
