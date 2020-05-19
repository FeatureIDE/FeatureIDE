# Description
Provides configuration generators, statistical computation for feature models, generation of feature relation graphs, a collaboration view, and a configuration map view.


# Structure


| Plugin   | Description |
| -------- | --------    |
| de.ovgu.featureide.ui.actions| Contains several actions for managing color schemes and generating configurations/samples|
| de.ovgu.featureide.ui.statistics | Contains the classes required for the statistics view that describes semantical and syntatical properties of a feature model |
| de.ovgu.featureide.ui.views.collaboration | Contains the classes required for the collobaration view    |
| de.ovgu.featureide.ui.configMap | Contains the classes required for the configuration map |
| de.ovgu.featureide.ui.wizards	| Contains several wizards for creating new FeatureIDE resources (e.g. feature projects/models) |


# Plugin.xml


| Extension Name | Extension ID                            | Description |
|----------------|-----------------------------------------|-------------| 
| -   | - |-								|



# Important Classes

### Generate Configurations
* [BuildProductWizard](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/actions/generator/BuildProductsWizard.java)
* [ConfigurationBuilder](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/actions/generator/ConfigurationBuilder.java)

### Sampling Algorithms
* [CHVATAL](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/actions/generator/configuration/CHVATALConfigurationGenerator.java)
* [CASA](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/actions/generator/configuration/CASAConfigurationGenerator.java)
* [ACNF](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/actions/generator/configuration/ACNFConfigurationGenerator.java)
* [ICPL](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/actions/generator/configuration/ICPLConfigurationGenerator.java)
* [TWise](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/actions/generator/configuration/TWiseConfigurationGenerator.java)


### Statistics View
* [FeatureStatisticsView](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/statistics/ui/FeatureStatisticsView.java)
* [ContentProvider](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/statistics/core/ContentProvider.java)
* [StatisticsSemanticalFeatureModel](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/statistics/core/composite/lazyimplementations/StatisticsSemanticalFeatureModel.java)
* [StatisticsSyntacticalFeatureModel](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/statistics/core/composite/lazyimplementations/StatisticsSyntacticalFeatureModel.java)

### Collaboration Diagram
* [CollaborationView](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/views/collaboration/CollaborationView.java)
* [CollaborationOutline](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/views/collaboration/outline/CollaborationOutline.java)

### Configuration Map
* [ConfigurationMap](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/views/configMap/ConfigurationMap.java)
* [ConfigurationMapTreeContentProvider](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/views/configMap/ConfigurationMapTreeContentProvider.java)

### Wizards
* [NewConfigurationFileWizard](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/wizards/NewConfigurationFileWizard.java)
* [NewFeatureProjectWizard](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/wizards/NewFeatureProjectWizard.java)
* [NewFeatureIDEFileWizard](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.ui/src/de/ovgu/featureide/ui/wizards/NewFeatureIDEFileWizard.java)
