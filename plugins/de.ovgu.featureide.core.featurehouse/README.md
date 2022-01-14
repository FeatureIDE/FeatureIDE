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

# Plugin.xml

The FeatureHouse plugin does not offer any extension points.


# Important Classes

* [FeatureHouseComposer](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core.featurehouse/src/de/ovgu/featureide/featurehouse/FeatureHouseComposer.java)
* [FeatureHouseCorePlugin](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core.featurehouse/src/de/ovgu/featureide/featurehouse/FeatureHouseCorePlugin.java)
