# Description

de.ovgu.featureide.core.antenna uses the Antenna Preprocessor to compose Java software products. Requires the Antenna library (https://github.com/FeatureIDE/Antenna) to work.

- Parses files for preprocessor directives and creates software products from current configuration.
- Manages error markers (wrong syntax) and warning markers (dead code blocks, superfluous preprocessor annotations).

# Structure


| Plugin   | Description |
| -------- | --------    |
| de.ovgu.featureide.core.antenna     | Creates java files from configurations. Also finds dead code blocks, and manages file markers.  |
| de.ovgu.featureide.core.antenna.documentation     | Contains documentation comment parser. |
| de.ovgu.featureide.core.antenna.model     | Builds the feature structure tree model for antenna projects.     |


# Plugin.xml

The Antenna plugin does not offer any extension points.


# Important Classes

* [AntennaCorePlugin](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core.antenna/src/de/ovgu/featureide/antenna/AntennaCorePlugin.java)
* [AntennaPreprocessor](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core.antenna/src/de/ovgu/featureide/antenna/AntennaPreprocessor.java)
