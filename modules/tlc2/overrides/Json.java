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
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetOfFcnsValue;
import tlc2.value.impl.SetOfRcdsValue;
import tlc2.value.impl.SetOfTuplesValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.SubsetValue;
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
   * @param path the JSON file path
   * @return a tuple of JSON values
   */
  @TLAPlusOperator(identifier = "JsonDeserialize", module = "Json", warn = false)
  public static IValue deserialize(final StringValue path) throws IOException {
    ObjectMapper mapper = new ObjectMapper();
    List<Value> values = new ArrayList<>();
    try (BufferedReader reader = new BufferedReader(new FileReader(new File(path.val.toString())))) {
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
   * @param path  the file to which to write the values
   * @param value the values to write
   * @return a boolean value indicating whether the serialization was successful
   */
  @TLAPlusOperator(identifier = "JsonSerialize", module = "Json", warn = false)
  public static BoolValue serialize(final StringValue path, final TupleValue value) throws IOException {
    File file = new File(path.val.toString());
    file.getParentFile().mkdirs();
    try (BufferedWriter writer = new BufferedWriter(new FileWriter(new File(path.val.toString())))) {
      for (int i = 0; i < value.elems.length; i++) {
        writer.write(getNode(value.elems[i]).toString() + "\n");
      }
    }
    return BoolValue.ValTrue;
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
    } else if (value instanceof SetEnumValue) {
      return getArrayNode((SetEnumValue) value);
    } else if (value instanceof SetOfRcdsValue) {
      return getArrayNode((SetEnumValue) ((SetOfRcdsValue) value).toSetEnum());
    } else if (value instanceof SetOfTuplesValue) {
      return getArrayNode((SetEnumValue) ((SetOfTuplesValue) value).toSetEnum());
    } else if (value instanceof SetOfFcnsValue) {
      return getArrayNode((SetEnumValue) ((SetOfFcnsValue) value).toSetEnum());
    } else if (value instanceof SubsetValue) {
      return getArrayNode((SetEnumValue) ((SubsetValue) value).toSetEnum());
    } else if (value instanceof IntervalValue) {
      return getArrayNode((SetEnumValue) ((IntervalValue) value).toSetEnum());
    } else {
      throw new IOException("Cannot convert value: unsupported value type " + value.getClass().getName());
    }
  }

  /**
   * Returns a boolean indicating whether the given value is a valid sequence.
   *
   * @param value the value to check
   * @return indicates whether the value is a valid sequence
   */
  private static boolean isValidSequence(FcnRcdValue value) {
    if (value.intv != null) {
      return value.intv.low == 1 && value.intv.high == value.domain.length;
    }
    for (Value domain : value.domain) {
      if (!(domain instanceof IntValue)) {
        return false;
      }
    }
    value.normalize();
    for (int i = 0; i < value.domain.length; i++) {
      if (((IntValue) value.domain[i]).val != (i + 1)) {
        return false;
      }
    }
    return true;
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
      throw new IOException("Cannot convert value: unsupported value type " + value.getClass().getName());
    }
  }

  /**
   * Converts the given record value to a {@code JsonNode}, recursively converting values.
   *
   * @param value the value to convert
   * @return the converted {@code ObjectNode}
   */
  private static JsonNode getObjectNode(FcnRcdValue value) throws IOException {
    if (isValidSequence(value)) {
      return getArrayNode(value);
    }

    Map<String, JsonNode> entries = new HashMap<>();
    for (int i = 0; i < value.domain.length; i++) {
      Value domainValue = value.domain[i];
      if (domainValue instanceof StringValue) {
        entries.put(((StringValue) domainValue).val.toString(), getNode(value.values[i]));
      } else {
        entries.put(domainValue.toString(), getNode(value.values[i]));
      }
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
   * Recursively converts the given value to an {@code ArrayNode}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonNode}
   */
  private static JsonNode getArrayNode(IValue value) throws IOException {
    if (value instanceof TupleValue) {
      return getArrayNode((TupleValue) value);
    } else if (value instanceof FcnRcdValue) {
      return getArrayNode((FcnRcdValue) value);
    } else if (value instanceof FcnLambdaValue) {
      return getArrayNode((FcnRcdValue) ((FcnLambdaValue) value).toFcnRcd());
    } else if (value instanceof SetEnumValue) {
      return getArrayNode((SetEnumValue) value);
    } else if (value instanceof SetOfRcdsValue) {
      return getArrayNode((SetEnumValue) ((SetOfRcdsValue) value).toSetEnum());
    } else if (value instanceof SetOfTuplesValue) {
      return getArrayNode((SetEnumValue) ((SetOfTuplesValue) value).toSetEnum());
    } else if (value instanceof SetOfFcnsValue) {
      return getArrayNode((SetEnumValue) ((SetOfFcnsValue) value).toSetEnum());
    } else if (value instanceof SubsetValue) {
      return getArrayNode((SetEnumValue) ((SubsetValue) value).toSetEnum());
    } else if (value instanceof IntervalValue) {
      return getArrayNode((SetEnumValue) ((IntervalValue) value).toSetEnum());
    } else {
      throw new IOException("Cannot convert value: unsupported value type " + value.getClass().getName());
    }
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
   * Converts the given record value to an {@code ArrayNode}.
   *
   * @param value the value to convert
   * @return the converted {@code ArrayNode}
   */
  private static JsonNode getArrayNode(FcnRcdValue value) throws IOException {
    if (!isValidSequence(value)) {
      return getObjectNode(value);
    }

    value.normalize();
    List<JsonNode> elements = new ArrayList<>(value.values.length);
    for (int i = 0; i < value.values.length; i++) {
      elements.add(getNode(value.values[i]));
    }
    return new ArrayNode(new JsonNodeFactory(true), elements);
  }

  /**
   * Converts the given tuple value to an {@code ArrayNode}.
   *
   * @param value the value to convert
   * @return the converted {@code ArrayNode}
   */
  private static JsonNode getArrayNode(SetEnumValue value) throws IOException {
    value.normalize();
    Value[] values = value.elems.toArray();
    List<JsonNode> elements = new ArrayList<>(values.length);
    for (int i = 0; i < values.length; i++) {
      elements.add(getNode(values[i]));
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
        throw new IOException("Cannot convert value: unsupported JSON type " + node.getNodeType());
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

