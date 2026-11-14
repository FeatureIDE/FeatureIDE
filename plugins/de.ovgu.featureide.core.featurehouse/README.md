# Description

de.ovgu.featureide.core.featurehouse uses FeatureHouse to compose Java software products. 

- Generates software products by superimposing feature folders with the FeatureHouse algorithm.

# Structure


| Plugin   | Description |
| -------- | --------    |
| de.ovgu.featureide.core.featurehouse     | Creates java files from with configurations. Controls the life cycle of FeatureHouse projects |
| de.ovgu.featureide.core.featurehouse.errorpropagation     | Propagates error markers for composed files to source files. |
| de.ovgu.featureide.core.featurehouse.model     | Builds the feature structure tree model for FeatureHouse projects.     |
| de.ovgu.featureide.core.featurehouse.ui.handlers     | Handler classes for actions specific to FeatureHouse.     |

# Java Grammar of FeatureHouse

`lib/FeatureHouse.jar` parses Java with the JavaCC grammar in [featurehouse-grammar/java15.jj](featurehouse-grammar/java15.jj).
In addition to Java 1.5, it supports the following newer syntax inside methods and field initializers:

- Java 7: diamond operator (`<>`), try-with-resources, multi-catch, binary literals and underscores in number literals
- Java 8: lambda expressions, method references, intersection casts
- Java 14: switch expressions, `case ... ->` rules, `yield`
- Java 15: text blocks
- Java 16/21: pattern matching for `instanceof` and `switch` (type and record patterns, `when` guards, `case null`)

New declaration-level syntax (e.g. records, sealed classes, default methods, modules) is not supported yet, because it also needs composition rules.
After changing the grammar, run `sh featurehouse-grammar/rebuild-java-parser.sh` to regenerate the parser classes inside the jar. It needs a JDK 21 or newer. Close Eclipse first, as it locks the jar.

The grammar is tested by `TJavaParser` and `TJavaComposition` in `tests/de.ovgu.featureide.core.featurehouse-test` (package `de.ovgu.featureide.featurehouse.parser`).

# Plugin.xml

The FeatureHouse plugin does not offer any extension points.


# Important Classes

* [FeatureHouseComposer](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core.featurehouse/src/de/ovgu/featureide/featurehouse/FeatureHouseComposer.java)
* [FeatureHouseCorePlugin](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core.featurehouse/src/de/ovgu/featureide/featurehouse/FeatureHouseCorePlugin.java)
