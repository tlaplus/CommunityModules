import tlc2.value.impl.*;

import java.io.*;
import java.util.*;

public class ExternalFunctionParser {
  // @TLAPlusOperator(identifier = "ExFunParser", module = "ExternalFunctionParser")
  public static Value ExFunParser(final StringValue absolutePath) throws IOException {
    // read the log file at [absolutePath]
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    // initialize arrays for input values [domain] and output [values]
    List<IntValue> domain = new ArrayList<>();
    List<IntValue> values = new ArrayList<>();
    try {
      String line = br.readLine();
      while (line != null) {
        // split string on seperator into array of input and output values
        String[] lnarr = line.split(", ");
        // first parsed value is an input
        IntValue x = IntValue.gen(Integer.parseInt(lnarr[0]));
        // check if [domain] already contains this value
        if (!domain.contains(x)) {
          // if unique, add this value
          domain.add(x);
          // second parsed value is the corresponding output
          values.add(IntValue.gen(Integer.parseInt(lnarr[1])));
        }
        // else, skip it
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    // return the function which maps each input to its corresponding output
    return new FcnRcdValue(domain.toArray(new Value[0]), values.toArray(new Value[0]), true);
  }
}
