Community Repository
====================

This is an open repository dedicated to **contributions from the TLA+ commmunity**.
Here you are able to submit the snippets, operators, and modules that you wrote for
your specifications and that you want to share with the rest of the TLA+ community.

How to use it
-------------

Just copy & paste the snippet, the operators or the set of modules you are interested in.

Alternatively, you can download a [library archive](https://github.com/tlaplus/CommunityModules/releases) and add it to TLC's or the Toolbox's *TLA+ library path*.  The advantage of the library archive is that TLC will evaluate an operator faster if the operator comes with a (Java) implementation (see e.g. [SequencesExt.Java](https://github.com/tlaplus/CommunityModules/blob/master/modules/SequencesExt.java)).  Run TLC with ```-DTLA-Library=/path/to/lib/archive``` or add the library archive to the Toolbox (```File > Preferences > TLA+ Preferences > TLA+ library path locations```).

Being a community-driven repository puts the community in charge to check the validity and correctness of submissions. The maintainers of this repository will try to keep this place in order, but we can't guarantee the quality of the
modules and therefore cannot provide any assistance on eventual malfunctions.

Contributing
------------

If you have one or more snippets, operators, or modules you'd like to share, please make
a pull request and we'll take care of it eventually.

Before submitting your request make sure that:
* Your contribution is working.
* Your contribution is unique (or better): check whether someone already provided a similar solution.
* Your contribution is relevant to the project and actually adds some value.

We take the discretion to approve or reject submissions at our will.

Download
--------

[![Build Status](https://dev.azure.com/tlaplus/tlaplus/_apis/build/status/tlaplus.CommunityModules?branchName=master)](https://dev.azure.com/tlaplus/tlaplus/_build/latest?definitionId=4&branchName=master)
