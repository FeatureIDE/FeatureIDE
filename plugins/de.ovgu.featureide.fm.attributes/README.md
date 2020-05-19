# Description
de.ovgu.featureide.fm.attributes introduces extended feature models (EFM) and extended configurations (EC) into FeatureIDE. Besides the new formats for EFM and EC it provides the attribute view to manage the attributes of EFMs.

# Structure

| Plugin   | Description |
| -------- | --------    |
| de.ovgu.featureide.fm.attributes.base | Contains the foundations for attributes and extended feature models.     |
| de.ovgu.featureide.fm.attributes.composer   | Contains the new composer for extended feature models that dictate how to build 'Extended Feature Modeling' projects. Further it contains the regex for valid feature names.  |
| de.ovgu.featureide.fm.attributes.computations   | Contains the outline extension to compute statistics for attributes in extended configuration. |
| de.ovgu.featureide.fm.attributes.formula   | Contains a heuristics used to compute attribute ranges |
| de.ovgu.featureide.fm.attributes.formula   | Contains a heuristics used to compute attribute ranges |
| de.ovgu.featureide.fm.attributes.view   | Contains the attribute view that enables users to manage the attributes for extended feature models and extended configurations. |


# Plugin.xml

### Provided Extension Points:

- none

### Used Extension Points:

| Extension Point &                                           <br>Class                                 | Description                                                                                         |
|-------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------| 
| de.ovgu.featureide.fm.core.FMFormat                        <br>`XmlExtendedFeatureModelFormat`        | Adds the xml-based format for extended feature models.                                               |
| de.ovgu.featureide.fm.core.FMFactory                       <br>`ExtendedFeatureModelFactory`          | Adds a new factory which is responsible to create extended feature models.                          |
| de.ovgu.featureide.fm.core.ConfigFormat                    <br>`XmlExtendedConfFormat`                | Adds the xml-based format for extended configurations.                                               |
| de.ovgu.featureide.fm.ui.ConfigurationOutlineEntry         <br>`AttributeComputationBundle`           | Extends the outline for configurations by computing statistics such as `Number of selected features`.|
| de.ovgu.featureide.fm.core.FMComposer                      <br>`ExtendedFeatureModelingFMExtension`   | Adds 'Extended Feature Modeling' as a composer for feature models.                             |
| de.ovgu.featureide.core.composers                          <br>`AttributeComputationBundle`           | Adds 'Extended Feature Modeling' as a composer for FeatureIDE Projects.  

# Important Classes

### Feature Attributes
- AbstractFeatureAttributeFactory
- IFeatureAttribute
- FeatureAttribute

### Extended Feature Models
- ExtendedFeatureModelFactory
- ExtendedFeatureModel
- ExtendedFeature
- XmlExtendedFeatureModelFormat

### Extended Configurations
- ExtendedConfiguration
- ExtendedSelectableFeature
- XmlExtendedConfFormat

### Feature Attribute View
- FeatureAttributeView
- FeatureAttributeContentProvider
- FeatureAttributeViewSelectionFilter

### Outline Attributes Computation
- IAttributeComputation
- AttributeComputationBundle
