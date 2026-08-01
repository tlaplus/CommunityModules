import tlc2.value.impl.*;
import util.UniqueString;

import java.io.*;
import java.util.*;

public class ExternalRecordParser {
  // @TLAPlusOperator(identifier = "ExRcdParser", module = "ExternalRecordParser")
  public static Value ExRcdParser(final StringValue absolutePath) throws IOException {
    // read the log file at [absolutePath]
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    // initialize arrays for input values [domain] and output [values]
    List<UniqueString> fields = new ArrayList<>();
    List<Value> values = new ArrayList<>();
    try {
      String line = br.readLine();
      while (line != null) {
        // split string on seperator into array of filed and value
        String[] lnarr = line.split(" : ");
        // first parsed value is a field
        fields.add(UniqueString.uniqueStringOf(lnarr[0]));
        // second parsed value is the corresponding value
        if (lnarr[1].equals("false") || lnarr[1].equals("true")) {
          values.add(new BoolValue(Boolean.parseBoolean(lnarr[1])));
        } else {
          values.add(IntValue.gen(Integer.parseInt(lnarr[1])));
        }
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    // return the record which maps each field to its corresponding value
    return new RecordValue(fields.toArray(new UniqueString[0]), values.toArray(new Value[0]), true);
  }
}
