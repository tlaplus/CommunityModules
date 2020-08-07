Community Repository
====================

[This is an open repository](https://github.com/tlaplus/CommunityModules/) dedicated to **contributions from the TLA+ commmunity**.
Here you are able to submit the snippets, operators, and modules that you wrote for
your specifications and that you want to share with the rest of the TLA+ community.

How to use it
-------------

Just copy & paste the snippet, the operators or the set of modules you are interested in.

Alternatively, you can download a [library archive](https://github.com/tlaplus/CommunityModules/releases) and add it to TLC's or the Toolbox's *TLA+ library path*.  The advantage of the library archive is that TLC will evaluate an operator faster if the operator comes with a (Java) implementation (see e.g. [SequencesExt.Java](https://github.com/tlaplus/CommunityModules/blob/master/modules/tlc2/overrides/SequencesExt.java)).  Run TLC with ```-DTLA-Library=/path/to/lib/archive``` or add the library archive to the Toolbox (```File > Preferences > TLA+ Preferences > TLA+ library path locations```).

Being a community-driven repository puts the community in charge to check the validity and correctness of submissions. The maintainers of this repository will try to keep this place in order, but we can't guarantee the quality of the
modules and therefore cannot provide any assistance on eventual malfunctions.

Contributing
------------

If you have one or more snippets, operators, or modules you'd like to share, please open an issue or create
a pull request.  Before submitting your operator or module, please consider adding documentation.  The more documentation there is, the more likely it is that someone will find it useful.

Download
--------

![CI](https://github.com/tlaplus/CommunityModules/workflows/CI/badge.svg)
