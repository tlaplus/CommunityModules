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
 *   William Schultz - initial API and implementation
 ******************************************************************************/
import util.UniqueString;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.Value;

public final class SVG {

	private SVG() {
		// no-instantiation!
	}

	/**
	 * Converts an SVG element to its string representation.
	 * 
	 * In TLA+, an SVG object must be represented as a record with the following format:
	 * 
	 * [ name 		|-> <string>
	 *	 attrs 		|-> <record>
	 *	 children 	|-> <tuple>
	 *	 innerText 	|-> <string> ]
	 */
	public static Value SVGElemToString(Value elem) throws Exception {
		if (!(elem instanceof RecordValue)) {
			throw new Exception(
					"An SVG element must be a record. Value given is of type: " + elem.getClass().toString());
		}

		RecordValue frv = (RecordValue) elem;

		// Get 'name'.
		StringValue nameVal = (StringValue) frv.apply(new StringValue("name"), 0);
		String name = nameVal.getVal().toString();

		// Get 'attrs'. We convert it to 'RecordValue' type, which we expect should always be possible.
		Value attrsVal = frv.apply(new StringValue("attrs"), 0);
		RecordValue attrs = (RecordValue)(attrsVal.toRcd());
		if(attrs == null){
			throw new Exception("Was unable to convert element to a record: " + attrsVal.toString());
		}
		String attrStr = "";
		for (UniqueString us : attrs.names) {
			attrStr += " ";
			attrStr += us.toString();
			attrStr += "=";
			String v = ((StringValue) attrs.apply(new StringValue(us), 0)).getVal().toString();
			// Quote all SVG attribute values. Technically, attribute values in HTML
			// don't always need to be quoted, but we use quotes so we can handle all
			// possible values. We single quote them to play nice with TLC string formatting.
			attrStr += "'" + v + "'";
		}

		// Get 'children'. We convert it to a TupleValue, which we expect should
		// always be possible.
		Value childrenVal = frv.apply(new StringValue("children"), 0);
		TupleValue children = (TupleValue)(childrenVal.toTuple());
		if(children == null){
			throw new Exception("Was unable to convert element to a tuple: " + childrenVal.toString());
		}
		String childStr = "";
		for (Value child : children.elems) {
			StringValue cv = (StringValue)SVGElemToString(child);
			childStr += cv.getVal().toString();
		}

		// Get 'innerText'.
		// This is raw text placed inside the current SVG element. For example, if
		// 'innerText' was "hello", then we would output an SVG element like:
		//
		// <elem>hello</elem>
		//
		// For SVG elements that are not of type <text>, text inside an element is not
		// rendered, so this property is only meaningful for <text> elements. It is expected
		// to be empty for all other element types, but since it's not rendered, we don't 
		// explicitly disallow it.
		StringValue innerTextVal = (StringValue) frv.apply(new StringValue("innerText"), 0);
		String innerText = innerTextVal.getVal().toString();

		// Produce the SVG element string.
		String svg = String.format("<%s%s>", name, attrStr);
		svg += innerText;
		svg += childStr;
		svg += String.format("</%s>", name);
		return new StringValue(svg);
	}
}
