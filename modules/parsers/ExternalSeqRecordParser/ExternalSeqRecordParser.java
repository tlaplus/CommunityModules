import tlc2.value.impl.*;
import util.UniqueString;

import java.io.*;
import java.util.*;

public class ExternalSeqRecordParser {
  // @TLAPlusOperator(identifier = "ExSeqRcdParser", module = "ExternalSeqRecordParser")
  public static Value ExSeqRcdParser(final StringValue absolutePath) throws IOException {
    // read the log file at [absolutePath]
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    // initialize array for all parsed records
    List<RecordValue> rcdSeq = new ArrayList<>();
    try {
      String line = br.readLine();
      while (line != null) {
        // initialize arrays for field values [fields] and [values]
        List<UniqueString> fields = new ArrayList<>();
        List<Value> values = new ArrayList<>();
        // split string on seperator into array of filed and value
        String[] lnarr = line.split(", ");
        // parse each entry of [lnarr] as a field-value pair
        parsePair(lnarr[0].split(" : "), fields, values);
        parsePair(lnarr[1].split(" : "), fields, values);
        // add record to the sequence
        rcdSeq.add(new RecordValue(fields.toArray(new UniqueString[0]), values.toArray(new Value[0]), true));
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    // return the aggregated sequence of records
    return new TupleValue(rcdSeq.toArray(new Value[0]));
  }

  private static void parsePair(String[] pair, List<UniqueString> fields, List<Value> values) {
    fields.add(UniqueString.uniqueStringOf(pair[0]));
    if (pair[1].equals("false") || pair[1].equals("true")) {
      values.add(new BoolValue(Boolean.parseBoolean(pair[1])));
    } else {
      values.add(IntValue.gen(Integer.parseInt(pair[1])));
    }
  }
}
