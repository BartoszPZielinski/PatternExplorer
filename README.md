Complex event processing (CEP) systems  discover in the incoming event stream   occurrences of 
patterns of events (called complex events) which indicate threats, opportunities, or  necessity of some action. Sufficiently complex patterns  may become  hard to understand, and even simple patterns may contain subtle errors with respect to their intended meaning.   

**PatternExplorer** tool helps to find errors in patterns.
The tool compiles patterns (regular language-like) into a non-deterministic automata with variables.
Compiled patterns can be matched with streams of events. More importantly, using extended narrowing the tool can generate effectively symbolic event sequences satisfying a pattern. Generated sequences can then be matched with another pattern to check if there are any unintended matching complex events.
Of particular note is our efficient representation of skipped events in generated symbolic streams which avoids creation of spurious instances and reduces the search space. A user-friendly web interface provides access to most important functionalities.

A complete documentation can be found in the [project page](https://bartoszpzielinski.github.io/PatternExplorer/)

## Authors

Bartosz Zieliński bartosz.zielinski@fis.uni.lodz.pl 
Paweł Maślanka pawel.maslanka@fis.uni.lodz.pl