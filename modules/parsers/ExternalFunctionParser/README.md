# External Function Parser

This small project provides a utility for parsing an `int -> int` function, computed externally and supplied as a log of comma-separated input-output values (see [examples](./examples)). This function can then be injected it into a TLA+ spec as a `CONSTANT`.

[ExternalFunctionParser.java](ExternalFunctionParser.java) defines the Java class `ExternalFunctionParser` containing the `ExFunParser` function which parses a log of input-output pairs into a TLA+ function

[ExternalFunctionParser.tla](ExternalFunctionParser.tla) is a dummy declaration for the `ExFunParser` function which is overriden by the Java function of the same name

## Note on TLA+ Toolbox

When parsing any provided examples *from the TLA+ toolbox*, one must modify the path accordingly. For example, to parse the function in `./examples/ex0.txt` from the toolbox, we evaluate

```
ExFunParser("../../examples/ex0.txt")
```
