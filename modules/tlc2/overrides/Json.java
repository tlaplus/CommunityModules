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

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.BooleanNode;
import com.fasterxml.jackson.databind.node.IntNode;
import com.fasterxml.jackson.databind.node.JsonNodeFactory;
import com.fasterxml.jackson.databind.node.ObjectNode;
import com.fasterxml.jackson.databind.node.TextNode;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnLambdaValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.UniqueString;

/**
 * Module overrides for operators to read and write JSON.
 */
public class Json {

  /**
   * Encodes the given value as a JSON string.
   *
   * @param value the value to encode
   * @return the JSON string value
   */
  @TLAPlusOperator(identifier = "ToJson", module = "Json", warn = false)
  public static StringValue toJson(final IValue value) throws IOException {
    return new StringValue(getNode(value).toString());
  }

  /**
   * Encodes the given value as a JSON array string.
   *
   * @param value the value to encode
   * @return the JSON array string value
   */
  @TLAPlusOperator(identifier = "ToJsonArray", module = "Json", warn = false)
  public static StringValue toJsonArray(final IValue value) throws IOException {
    return new StringValue(getArrayNode(value).toString());
  }

  /**
   * Encodes the given value as a JSON object string.
   *
   * @param value the value to encode
   * @return the JSON object string value
   */
  @TLAPlusOperator(identifier = "ToJsonObject", module = "Json", warn = false)
  public static StringValue toJsonObject(final IValue value) throws IOException {
    return new StringValue(getObjectNode(value).toString());
  }

  /**
   * Deserializes a tuple of newline delimited JSON values from the given path.
   *
   * @param absolutePath the JSON file path
   * @return a tuple of JSON values
   */
  @TLAPlusOperator(identifier = "JsonDeserialize", module = "Json", warn = false)
  public static IValue deserialize(final StringValue absolutePath) throws IOException {
    ObjectMapper mapper = new ObjectMapper();
    List<Value> values = new ArrayList<>();
    try (BufferedReader reader = new BufferedReader(new FileReader(new File(absolutePath.val.toString())))) {
      String line = reader.readLine();
      while (line != null) {
        JsonNode node = mapper.readTree(line);
        values.add(getValue(node));
        line = reader.readLine();
      }
    }
    return new TupleValue(values.toArray(new Value[0]));
  }

  /**
   * Serializes a tuple of values to newline delimited JSON.
   *
   * @param absolutePath the file to which to write the values
   * @param value        the values to write
   */
  @TLAPlusOperator(identifier = "JsonSerialize", module = "Json", warn = false)
  public static void serialize(final StringValue absolutePath, final TupleValue value) throws IOException {
    try (BufferedWriter writer = new BufferedWriter(new FileWriter(new File(absolutePath.val.toString())))) {
      for (int i = 0; i < value.elems.length; i++) {
        writer.write(getNode(value.elems[i]).toString() + "\n");
      }
    }
  }

  /**
   * Recursively converts the given value to a {@code JsonNode}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonNode}
   */
  private static JsonNode getNode(IValue value) throws IOException {
    if (value instanceof RecordValue) {
      return getObjectNode((RecordValue) value);
    } else if (value instanceof TupleValue) {
      return getArrayNode((TupleValue) value);
    } else if (value instanceof StringValue) {
      return new TextNode(((StringValue) value).val.toString());
    } else if (value instanceof IntValue) {
      return new IntNode(((IntValue) value).val);
    } else if (value instanceof BoolValue) {
      return BooleanNode.valueOf(((BoolValue) value).val);
    } else if (value instanceof FcnRcdValue) {
      return getObjectNode((FcnRcdValue) value);
    } else if (value instanceof FcnLambdaValue) {
      return getObjectNode((FcnRcdValue) ((FcnLambdaValue) value).toFcnRcd());
    } else {
      throw new IOException("Cannot convert value: Unknown type");
    }
  }

  /**
   * Recursively converts the given value to an {@code ObjectNode}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonNode}
   */
  private static JsonNode getObjectNode(IValue value) throws IOException {
    if (value instanceof RecordValue) {
      return getObjectNode((RecordValue) value);
    } else if (value instanceof TupleValue) {
      return getObjectNode((TupleValue) value);
    } else if (value instanceof FcnRcdValue) {
      return getObjectNode((FcnRcdValue) value);
    } else if (value instanceof FcnLambdaValue) {
      return getObjectNode((FcnRcdValue) ((FcnLambdaValue) value).toFcnRcd());
    } else {
      throw new IOException("Cannot convert value: Unknown type");
    }
  }

  /**
   * Recursively converts the given value to an {@code ArrayNode}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonNode}
   */
  private static JsonNode getArrayNode(IValue value) throws IOException {
    if (value instanceof TupleValue) {
      return getArrayNode((TupleValue) value);
    } else {
      throw new IOException("Cannot convert value: Unknown type");
    }
  }

  /**
   * Converts the given record value to an {@code ObjectNode}, recursively converting values.
   *
   * @param value the value to convert
   * @return the converted {@code ObjectNode}
   */
  private static JsonNode getObjectNode(FcnRcdValue value) throws IOException {
    Map<String, JsonNode> entries = new HashMap<>();
    for (int i = 0; i < value.domain.length; i++) {
      entries.put(value.domain[i].toString(), getNode(value.values[i]));
    }
    return new ObjectNode(new JsonNodeFactory(true), entries);
  }

  /**
   * Converts the given record value to an {@code ObjectNode}.
   *
   * @param value the value to convert
   * @return the converted {@code ObjectNode}
   */
  private static JsonNode getObjectNode(RecordValue value) throws IOException {
    Map<String, JsonNode> entries = new HashMap<>();
    for (int i = 0; i < value.names.length; i++) {
      entries.put(value.names[i].toString(), getNode(value.values[i]));
    }
    return new ObjectNode(new JsonNodeFactory(true), entries);
  }

  /**
   * Converts the given tuple value to an {@code ObjectNode}.
   *
   * @param value the value to convert
   * @return the converted {@code ObjectNode}
   */
  private static JsonNode getObjectNode(TupleValue value) throws IOException {
    Map<String, JsonNode> entries = new HashMap<>();
    for (int i = 0; i < value.elems.length; i++) {
      entries.put(String.valueOf(i), getNode(value.elems[i]));
    }
    return new ObjectNode(new JsonNodeFactory(true), entries);
  }

  /**
   * Converts the given tuple value to an {@code ArrayNode}.
   *
   * @param value the value to convert
   * @return the converted {@code ArrayNode}
   */
  private static JsonNode getArrayNode(TupleValue value) throws IOException {
    List<JsonNode> elements = new ArrayList<>(value.elems.length);
    for (int i = 0; i < value.elems.length; i++) {
      elements.add(getNode(value.elems[i]));
    }
    return new ArrayNode(new JsonNodeFactory(true), elements);
  }

  /**
   * Recursively converts the given {@code JsonNode} to a TLC value.
   *
   * @param node the {@code JsonNode} to convert
   * @return the converted value
   */
  private static Value getValue(JsonNode node) throws IOException {
    switch (node.getNodeType()) {
      case ARRAY:
        return getTupleValue(node);
      case OBJECT:
        return getRecordValue(node);
      case NUMBER:
        return IntValue.gen(node.asInt());
      case BOOLEAN:
        return new BoolValue(node.asBoolean());
      case STRING:
        return new StringValue(node.asText());
      case NULL:
        return null;
      default:
        throw new IOException("Cannot convert tuple value: Unknown type");
    }
  }

  /**
   * Converts the given {@code JsonNode} to a tuple.
   *
   * @param node the {@code JsonNode} to convert
   * @return the tuple value
   */
  private static TupleValue getTupleValue(JsonNode node) throws IOException {
    List<Value> values = new ArrayList<>();
    for (int i = 0; i < node.size(); i++) {
      values.add(getValue(node.get(i)));
    }
    return new TupleValue(values.toArray(new Value[0]));
  }

  /**
   * Converts the given {@code JsonNode} to a record.
   *
   * @param node the {@code JsonNode} to convert
   * @return the record value
   */
  private static RecordValue getRecordValue(JsonNode node) throws IOException {
    List<UniqueString> keys = new ArrayList<>();
    List<Value> values = new ArrayList<>();
    Iterator<Map.Entry<String, JsonNode>> iterator = node.fields();
    while (iterator.hasNext()) {
      Map.Entry<String, JsonNode> entry = iterator.next();
      keys.add(UniqueString.uniqueStringOf(entry.getKey()));
      values.add(getValue(entry.getValue()));
    }
    return new RecordValue(keys.toArray(new UniqueString[0]), values.toArray(new Value[0]), false);
  }
}

