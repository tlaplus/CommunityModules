# External Record Parser

This small project provides a utility for parsing a record `[ a : Int, b : BOOLEAN ]`, computed externally and supplied as a log of newline-separated field-value pairs (see [examples](./examples)). This function can then be injected it into a TLA+ spec as a `CONSTANT`.

[ExternalRecordParser.java](ExternalRecordParser.java) defines the Java class `ExternalRecordParser` containing the `ExRcdParser` function which parses a log of field-value pairs into a TLA+ function

[ExternalRecordParser.tla](ExternalRecordParser.tla) is a dummy declaration for the `ExRcdParser` function which is overriden by the Java function of the same name

## Note on TLA+ Toolbox

When parsing any provided examples *from the TLA+ toolbox*, one must modify the path accordingly. For example, to parse the function in `./examples/ex0.txt` from the toolbox, we evaluate

```
ExRcdParser("../../examples/ex0.txt")
```
