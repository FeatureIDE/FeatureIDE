# FeatureIDE

An extensible framework for feature-oriented software development

latest release:
[![Build Status](https://travis-ci.org/FeatureIDE/FeatureIDE.svg?branch=master)](https://travis-ci.org/FeatureIDE/FeatureIDE)

release candidate:
[![Build Status](https://travis-ci.org/FeatureIDE/FeatureIDE.svg?branch=release3.6)](https://travis-ci.org/FeatureIDE/FeatureIDE)

development branch:
[![Build Status](https://travis-ci.org/FeatureIDE/FeatureIDE.svg?branch=develop)](https://travis-ci.org/FeatureIDE/FeatureIDE)

## Plugins Overview

### FeatureIDE Core Plugins

| Plugin                                                                                                                       | Description                                                                                                                                                               |
|------------------------------------------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [de.ovgu.featureide.core](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core)             | Provides basic components for FeatureIDE projects and composer extensions.                                                                                                |
| [de.ovgu.featureide.ui](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.ui)                 | Provides configuration generators, statistical computation for feature models, generation of feature relation graphs, a collaboration view, and a configuration map view. |
| [de.ovgu.featureide.ui.android](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.ui.android) | Provides tools to convert an existing android project into a FeatureIDE project.                                                                                          |
| [de.ovgu.featureide.ui.mpl](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.ui.mpl)         | Provides tools to create multiple product line (MPL) projects.                                                                                                            |

### Feature Modeling

| Plugin                                                                                                                 | Description                                                                                             |
|------------------------------------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------|
| [de.ovgu.featureide.fm.core](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.fm.core) | Provides core components for feature modelling to create and analyze feature models and configurations. |
| [de.ovgu.featureide.fm.ui](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.fm.ui)     | Provides views and editors used for feature modeling. Also includes actions and commands used in them.  |

### Extended Feature Modeling

| Plugin                                                                                                                                                               | Description                                                          |
|----------------------------------------------------------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------------|
| [de.ovgu.featureide.fm.attributes](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.fm.attributes) | Provides support for extended feature models and feature attributes. |

### Composers

| Plugin                                                                                                                                                                       | Description                                                                                                                                                                                                                                                 |
|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [de.ovgu.featureide.core.runtime](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.runtime)                                             | Provides support for runtime variability using runtime parameters and property files.                                                                                                                                                                       |
| [de.ovgu.featureide.core.images](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.images)                                               | Provides a composer that creates variable images by overlaying selected images.                                                                                                                                                                             |
| [de.ovgu.featureide.core.framework](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.framework)                                         | Provides black-box frameworks with plug-ins.                                                                                                                                                                                                                |
| [br.ufal.ic.colligens](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/br.ufal.ic.colligens)                                                                   | Provides annotation-based development for C projects using the C preprocessor.                                                                                                                                                                              |
| [de.ovgu.featureide.core.antenna](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.antenna)                                             | Provides annotation-based development using the [Antenna](https://sourceforge.net/projects/antenna/) preprocessor.                                                                                                                                          |
| [de.ovgu.featureide.core.munge](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.munge)                                                 | Provides annotation-based development using the [Munge](https://github.com/sonatype/munge-maven-plugin) preprocessor.                                                                                                                                       |
| [de.ovgu.featureide.core.munge.android](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.munge.android)                                 | Provides tools to convert an existing Android project into a FeatureIDE project. Also provides annotation-based development using the [Munge](https://github.com/sonatype/munge-maven-plugin) preprocessor adapted for usage with android.                  |
| [de.ovgu.featureide.core.featurehouse](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.featurehouse)                                   | Provides feature-oriented programming (FOP) using [FeatureHouse](http://www.fosd.de/fh).                                                                                                                                                                    |
| [de.ovgu.featureide.core.ahead](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.ahead)                                                 | Provides feature-oriented programming (FOP) using the [AHEAD](http://www.cs.utexas.edu/users/schwartz/ATS.html) composer.                                                                                                                                   |
| [de.ovgu.featureide.core.conversion.ahead-featurehouse](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.conversion.ahead-featurehouse) | Provides a tool to convert AHEAD projects into FeatureHouse projects.                                                                                                                                                                                       |
| [de.ovgu.featureide.core.featurecpp](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.featurecpp)                                       | Provides feature-oriented programming (FOP) in form of a C++ preprocessor that turns [FeatureC++](http://wwwiti.cs.uni-magdeburg.de/iti_db/forschung/fop/featurec/) code into C++ code. Also adopts language concepts of aspect-oriented programming (AOP). |
| [de.ovgu.featureide.core.aspectj](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.aspectj)                                             | Provides aspect-oriented programming (AOP) using [AspectJ](https://www.eclipse.org/aspectj/).                                                                                                                                                               |

### Multiple Product Lines

| Plugin                                                                                                                            | Description                                                                                              |
|-----------------------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------------------|
| [e.ovgu.featureide.Cloneanalysis](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.Cloneanalysis) | Provides a tool to create migrated software product lines with support for feature-aware clone analysis. |
| [de.ovgu.featureide.core.mpl](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.core.mpl)          | WIP                                                                                                      |
| [de.ovgu.featureide.migration](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.migration)        | Provides components to migrate multiple projects into a single FeatureIDE project.                       |

### Examples 

| Plugin                                                                                                                   | Description                                                                                                                                                                                                                                                                          |
|--------------------------------------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [de.ovgu.featureide.examples](https://github.com/FeatureIDE/FeatureIDE/tree/develop/plugins/de.ovgu.featureide.examples) | Provides example projects showcasing different functionalities of FeatureIDE. These functionalities include each of the composers, different supported programming paradigms (AOP, FOP, etc.), and feature modeling concepts (extended Feature Models, Feature Model formats, etc.). |
