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

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;

public class CSV {

	@TLAPlusOperator(identifier = "CSVWrite", module = "CSV", minLevel = 1, warn = false)
	public static Value write(final StringValue template, final Value parameter, final StringValue absolutePath)
			throws IOException {
		final TupleValue tv = (TupleValue) parameter.toTuple();
		if (tv == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "CSVWrite", "sequence", Values.ppr(parameter.toString()) });
		}
		final Object[] params = Arrays.asList(tv.getElems()).stream().map(v -> v.toString())
				.toArray(size -> new Object[size]);
		Files.write(Paths.get(absolutePath.val),
				(String.format(template.val, params) + System.lineSeparator()).getBytes("UTF-8"),
				StandardOpenOption.CREATE, StandardOpenOption.APPEND);
		return BoolValue.ValTrue;
	}

	@TLAPlusOperator(identifier = "CSVRead", module = "CSV", minLevel = 1, warn = false)
	public static Value read(final Value columns, final StringValue delim, final StringValue absolutePath)
			throws IOException {
		
		final TupleValue tv = (TupleValue) columns.toTuple();
		if (tv == null) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "CSVRead", "sequence", Values.ppr(columns.toString()) });
		}

		final Path path = Paths.get(absolutePath.val);
		if (!path.toFile().exists()) {
			// There are zero records in a file that doesn't exist.
			return TupleValue.EmptyTuple;
		}
		
		final String[] names = Arrays.asList(tv.elems).stream().map(v -> ((StringValue) v).val)
				.collect(Collectors.toList()).toArray(String[]::new);

		final List<String> lines = Files.readAllLines(path);
		final Value[] records = new Value[lines.size()];
		for (int i = 0; i < lines.size(); i++) {
			StringValue[] values = Arrays.asList(lines.get(i).split(delim.val)).stream()
					.map(s -> new StringValue(s)).collect(Collectors.toList()).toArray(StringValue[]::new);
			records[i] = new RecordValue(names, values, false);
		}

		return new TupleValue(records);
	}

	@TLAPlusOperator(identifier = "CSVRecords", module = "CSV", minLevel = 1, warn = false)
	public static Value records(final StringValue absolutePath)
			throws IOException {
		final Path path = Paths.get(absolutePath.val);
		if (!path.toFile().exists()) {
			// There are zero records in a file that doesn't exist.
			return IntValue.ValZero;
		}
		try (Stream<String> stream = Files.lines(path, StandardCharsets.UTF_8)) {
			try {
				return IntValue.gen(Math.toIntExact(stream.count()));
			} catch (ArithmeticException e) {
				throw new EvalException(EC.TLC_MODULE_OVERFLOW,
						Long.toString(stream.count()));
			}
		}
	}
}
