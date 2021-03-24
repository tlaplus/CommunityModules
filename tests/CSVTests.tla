---------------------------- MODULE CSVTests ----------------------------
EXTENDS CSV, TLC, Sequences, IOUtils

Template ==
	\* '#' symbol is probably best separator for TLA+.
	"%1$s#%2$s#%3$s"

Value ==
	<< 42, "abc", [a |-> "a", b |-> "b"] >>

ToFile == 
	"build/tests/CSVWriteTest-" \o ToString(JavaTime) \o ".csv"

\* Write Value to ToFile then check success by reading with IOExec. 
ASSUME(
  CSVWrite(Template, Value, ToFile) 
  	=> 
  	  IOExec(<< "cat", ToFile >>).stdout = "42#\"abc\"#[a |-> \"a\", b |-> \"b\"]\n")

=============================================================================
                                                                    
