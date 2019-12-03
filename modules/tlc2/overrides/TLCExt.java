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

import java.util.Scanner;

import tla2sany.semantic.ExprOrOpArgNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Value;
import util.Assert;

public class TLCExt {

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
					String.format("Extend behavior of length %s with a \"%s\" step [%s]? (Yes/no/states/diff):",
							s0.getLevel(), action.getName(), action));

			final String nextLine = scanner.nextLine();
			if (nextLine.trim().isEmpty() || nextLine.toLowerCase().startsWith("y")) {
				return BoolValue.ValTrue;
			} else if (nextLine.charAt(0) == 's') {
				MP.printMessage(EC.TLC_MODULE_OVERRIDE_STDOUT,
						String.format("%s\n~>\n%s", s0.toString().trim(), s1.toString().trim()));
			} else if (nextLine.charAt(0) == 'd') {
				MP.printMessage(EC.TLC_MODULE_OVERRIDE_STDOUT, s1.toString(s0));
			} else if (nextLine.charAt(0) == 'n') {
				return BoolValue.ValFalse;
			}
		}
	}
}
