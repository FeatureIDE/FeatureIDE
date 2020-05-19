# Description
This plugin provides
* an editor to manage feature diagrams
* an editor to manage configurations
* a view to manage and create constraint separated from the feature model editor
* a view that provides information about changes in the feature model edditor
* an outline that provides additional information and and an alternative view for the configuration and feature model editor 

# Structure


| Plugin   | Description |
| -------- | --------    |
| de.ovgu.featureide.fm.ui.editors.configuration| Contains classes required for the configuration editor and pages.|
| de.ovgu.featureide.fm.ui.editors.featuremodel | Contains the classes required for the feature model editor including several actions and operations. |
| de.ovgu.featureide.fm.ui.views.constraintview | Contains the classes required for the constraint view that can be used as an alternative to constrainted included in the feature model editor.    |
| de.ovgu.featureide.fm.ui.views.outline | Contains the classes required for the FeatureIDE outline. The outline can be used for different views. This package included outline behavior for the feature model and configuration editor. |
| de.ovgu.featureide.fm.ui.views.featuremodeleditview | Contains the classes required for the Feature model edits view. The outline can be used for different views. This package included outline behavior for the feature model and configuration editor. |
| de.ovgu.featureide.fm.ui.wizards	| Contains several wizards that can be opened in the views mentioned above. |


# Plugin.xml

### Provided Extension Points
| Extension Name | Extension ID                            | Description |
|----------------|-----------------------------------------|-------------| 
| FeatureModelEditor      | de.ovgu.featureide.fm.ui.FeatureModelEditor | Introduce alternative feature model editors  |
| FmTreeContentProvider      | de.ovgu.fm.ui.views.outline.FmTreeContentProvider| Introduce alternative content provider for FeatureIDE outline  |
| FmLabelProvider      | de.ovgu.fm.ui.outline.FmLabelProvider | Introduce alternative label provider for FeatureIDE outline  |
| FeatureDiagram      | de.ovgu.featureide.fm.ui.FeatureDiagram | Introduce alternative feature model editors  |
| Language      | de.ovgu.featureide.fm.ui.language | Provide another language for FeatureIDE  |
| ConfigurationEditor      | de.ovgu.featureide.fm.ui.ConfigurationEditor | Introduce alternative configuration editors  |
| Outline      | de.ovgu.featureide.fm.ui.Outline | Introduce alternative feature model editors  |
| ConfigurationOutlineEntry      | de.ovgu.featureide.fm.ui.ConfigurationOutlineEntry | Add entries to the configuration outline |

### Used Extension Points
| Extension Point &                                           <br>Class                                 | Description                                                                                         |
|-------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------| 
| de.ovgu.featureide.fm.ui.Outline                       <br>`FMOutlineProvider`        | Provides an outline that can be used with the feature model editor.                                               |
| de.ovgu.featureide.fm.ui.Outline                     <br>`ConfigurationOutlineProvider`          | Provides an outline that can be used with the configuration editor.                           |



# Important Classes

### Feature Model Editor
* [FeatureModelEditor](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/editors/FeatureModelEditor.java)
* [FeatureDiagramEditor](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/editors/FeatureModelEditor.java)
* [IGraphicalFeature](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/editors/IGraphicalFeature.java)
* [IGraphicalConstraint](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/editors/IGraphicalConstraint.java)
* [CreateFeatureBelowAction](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/editors/featuremodel/actions/CreateFeatureBelowAction.java)
* [AutomatedCalculationsAction](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/editors/featuremodel/actions/calculations/AutomatedCalculationsAction.java)
* [CreateFeatureOperation](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/editors/featuremodel/operations/CreateFeatureOperation.java)

### Configuration Editor
* [ConfigurationEditor](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/editors/configuration/ConfigurationEditor.java)


### Constraint View
* [ConstraintViewController](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/views/constraintview/ConstraintViewController.java)
* [ConstraintView](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/views/constraintview/view/ConstraintView.java)
* [CreateConstraintInViewAction](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/views/constraintview/actions/CreateConstraintInViewAction.java)

### Feature Model Edit View
* [ViewContentProvider](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/views/featuremodeleditview/ViewContentProvider.java)

### FeatureIDE Outline
* [Outline](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/views/outline/custom/Outline.java)
* [IOutlineEntry](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/views/outline/IOutlineEntry.java)
* [FmOutlinePageContextMenu](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/views/outline/FmOutlinePageContextMenu.java)

### Wizards
* [SubtreeDependencyWizard](https://github.com/FeatureIDE/FeatureIDE/blob/develop/plugins/de.ovgu.featureide.fm.ui/src/de/ovgu/featureide/fm/ui/wizards/SubtreeDependencyWizard.java)


