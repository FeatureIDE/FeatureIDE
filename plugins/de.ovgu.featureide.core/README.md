# Description
de.ovgu.featureide.core provides 

- The structure of FeatureIDE projects (FeatureProject, FeatureIDE nature, FST, Signature). 
- Control over the creation and life cycle of FeatureIDE projects (CorePlugin).
- Extension point for composers and classes with basic functionality that need to be implemented by them.
- Functionality specifically for preprocessor-based composers (PPComposerExtensionClass).

# Structure


| Plugin   | Description |
| -------- | --------    |
| de.ovgu.featureide.core.builder     | Classes used by composers.     |
| de.ovgu.featureide.core.fstmodel     | Feature structure tree creates      |
| de.ovgu.featureide.core.signature     | TODO     |
| de.ovgu.featureide.core.featuremodeling     | Composer extension class for feature modeling. This class does not allow the actual composition of software, just feature modeling.     |

# Plugin.xml

Extension points:

| Extension Name | Extension ID                            | Description |
|----------------|-----------------------------------------|-------------| 
| composers      | de.ovgu.featureide.core.compositiontool |Add new composers to FeatureIDE.             |
| wizards      | de.ovgu.featureide.ui.wizard |Add new ways to setup featureIDE projects.             |


# Important Classes

* [CorePlugin](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core/src/de/ovgu/featureide/core/CorePlugin.java)
* [ComposerExtensionClass](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core/src/de/ovgu/featureide/core/builder/ComposerExtensionClass.java)
* [DefaultNewFeatureProjectWizardExtension](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core/src/de/ovgu/featureide/core/wizardextension/DefaultNewFeatureProjectWizardExtension.java)
* [ExtensibleFeatureProjectBuilder](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core/src/de/ovgu/featureide/core/builder/ExtensibleFeatureProjectBuilder.java)
* [FeatureModeling](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core/src/de/ovgu/featureide/core/featuremodeling/FeatureModeling.java)
* [FeatureProject](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core/src/de/ovgu/featureide/core/internal/FeatureProject.java)
* [FSTModel](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core/src/de/ovgu/featureide/core/fstmodel/FSTModel.java)
* [PPComposerExtensionClass](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.core/src/de/ovgu/featureide/core/builder/preprocessor/PPComposerExtensionClass.java)
