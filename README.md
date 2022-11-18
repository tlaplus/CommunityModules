Community Repository
====================

[This is an open repository](https://github.com/tlaplus/CommunityModules/) dedicated to **contributions from the TLA+ community**.
Here you can submit the snippets, operators, and modules that you wrote for your specifications and that you want to share with the rest of the TLA+ community.

(For us to gauge demand, please star (`eyes up and right`) this repository if you use the CommunityModules.)

The Modules
-----------

| Name  | Short description | Module Override? | Contributors |
| :--: | ---- | ---- | ---- |
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/Functions.tla">Functions.tla</a> | Notions about functions including injection, surjection, and bijection. |[&#10004;](https://github.com/tlaplus/CommunityModules/blob/master/modules/tlc2/overrides/Functions.java) | [@muenchnerkindl](https://github.com/muenchnerkindl), [@quicquid](https://github.com/quicquid),[@lemmy](https://github.com/lemmy) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/Folds.tla">Folds.tla</a> | Basic Fold operator. | | [@quicquid](https://github.com/quicquid), [@muenchnerkindl](https://github.com/muenchnerkindl) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/Graphs.tla">Graphs.tla</a> | Common operators on directed and undirected graphs. | | Leslie Lamport, [@lemmy](https://github.com/lemmy), [@muenchnerkindl](https://github.com/muenchnerkindl) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/SequencesExt.tla">SequencesExt.tla</a> | Various operators to manipulate sequences. | [&#10004;](https://github.com/tlaplus/CommunityModules/blob/master/modules/tlc2/overrides/SequencesExt.java)| [@muenchnerkindl](https://github.com/muenchnerkindl),[@lemmy](https://github.com/lemmy), [@hwayne](https://github.com/hwayne), [@quicquid](https://github.com/quicquid) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/Relation.tla">Relation.tla</a> | Basic operations on relations, represented as binary Boolean functions over some set S.| | [@muenchnerkindl](https://github.com/muenchnerkindl) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/FiniteSetsExt.tla">FiniteSetsExt.tla</a> | An Operator to do folds without having to use RECURSIVE. | &#10004;| [@hwayne](https://github.com/hwayne),[@lemmy](https://github.com/lemmy), [@quicquid](https://github.com/quicquid) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/Bitwise.tla">Bitwise.tla</a> | Bitwise And and shift-right. | [&#10004;](https://github.com/tlaplus/CommunityModules/blob/master/modules/tlc2/overrides/Bitwise.java) | [@lemmy](https://github.com/lemmy),[@pfeodrippe](https://github.com/pfeodrippe) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/DifferentialEquations.tla">DifferentialEquations.tla</a> | see page 178ff of [Specifying Systems](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf)| | Leslie Lamport | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/Json.tla">Json.tla</a> | Print TLA+ values as JSON values. | [&#10004;](https://github.com/tlaplus/CommunityModules/blob/master/modules/tlc2/overrides/Json.java)| [@kuujo](https://github.com/kuujo) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/SVG.tla">SVG.tla</a> | see https://github.com/will62794/tlaplus_animation | [&#10004;](https://github.com/tlaplus/CommunityModules/blob/master/modules/tlc2/overrides/SVG.java)| [@will62794](https://github.com/will62794), [@lemmy](https://github.com/lemmy) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/ShiViz.tla">ShiViz.tla</a> | Visualize error-traces of multi-process PlusCal algorithms with an [Interactive Communication Graphs](https://bestchai.bitbucket.io/shiviz/). |  | [@lemmy](https://github.com/lemmy) | 
| <a href="https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/TLCExt.tla">TLCExt.tla</a> | Assertion operators and experimental TLC features (now part of TLC). | [&#10004;](https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/module/TLCExt.java)| [@lemmy](https://github.com/lemmy), [@will62794](https://github.com/will62794) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/IOUtils.tla">IOUtils.tla</a> | Input/Output of TLA+ values & Spawn system commands from a spec. | [&#10004;](https://github.com/tlaplus/CommunityModules/blob/master/modules/tlc2/overrides/IOUtils.java) | [@lemmy](https://github.com/lemmy), [@lvanengelen](https://github.com/lvanengelen) | 
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/Combinatorics.tla">Combinatorics.tla</a> | (n choose k), factorial, .... | [&#10004;](https://github.com/tlaplus/CommunityModules/blob/master/modules/tlc2/overrides/Combinatorics.java) | [@lemmy](https://github.com/lemmy) |
| <a href="https://github.com/tlaplus/CommunityModules/blob/master/modules/BagsExt.tla">BagsExt.tla</a> | BagAdd, BagRemove, FoldBag, ... |  | [@muenchnerkindl](https://github.com/muenchnerkindl) | 


How to use it
-------------

You must be running [Java 9 or higher](https://github.com/tlaplus/CommunityModules/issues/34#issuecomment-756571840).

Just copy & paste the snippet, the operators, or the set of modules you are interested in.

Alternatively, clone this repository and pass ```-DTLA-Library=/path/to/CommunityModules/modules``` when running TLC.

Another option is to download a [library archive](https://github.com/tlaplus/CommunityModules/releases) and add it to TLC's or the Toolbox's *TLA+ library path*. The advantage of doing this is that TLC will evaluate an operator faster if the operator comes with a Java implementation (see e.g. [SequencesExt.Java](https://github.com/tlaplus/CommunityModules/blob/master/modules/tlc2/overrides/SequencesExt.java)). The latest release is at the stable URL https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules.jar.

If you are using the Toolbox, add the library archive under `File > Preferences > TLA+ Preferences > TLA+ library path locations`.
[![Screencast how to install the CommunityModules into the TLA+ Toolbox](https://img.youtube.com/vi/w9t6JnmxV2E/0.jpg)](https://www.youtube.com/watch?v=w9t6JnmxV2E)

If you are using the [VS Code extension](https://github.com/tlaplus/vscode-tlaplus), a recent version of the community modules is bundled with the nightly build. If you are not using the nightly build or need to use another version, see [this](https://github.com/tlaplus/vscode-tlaplus/issues/249).

If you are running TLC via tla2tools.jar, ensure the JAR is on the *classpath*: either place it next to tla2tools.jar or add it explicitly with `java -cp tla2tools.jar:CommunityModules-deps.jar ...`.

Being a community-driven repository puts the community in charge of checking the validity and correctness of submissions. The maintainers of this repository will try to keep this place in order. Still, we can't guarantee the quality of the modules and, therefore, cannot provide any assistance on eventual malfunctions.

Contributing
------------

If you have one or more snippets, operators, or modules you'd like to share, please open an issue or create
a pull request.  Before submitting your operator or module, please consider adding documentation.  The more documentation there is, the more likely it is that someone will find it useful.

If you change an existing module and tests start failing, check all tests that assert (usually `AssertError` operator) specific error messages, i.e., line numbers and module names.
Note that even an unrelated change further up in the file might have changed the line number and could lead to a failing test case.

Test
------------
Run

``` shell
ant test
```

Download
--------

![CI](https://github.com/tlaplus/CommunityModules/workflows/CI/badge.svg)
