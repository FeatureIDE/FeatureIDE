package de.ovgu.featureide.fm.attributes.base.impl;

import de.ovgu.featureide.fm.core.base.impl.FeatureModel;

public class ExtendedFeatureModel extends FeatureModel {

	protected ExtendedFeatureModel(ExtendedFeatureModel copyFeatureModel, ExtendedFeature newRoot) {
		super(copyFeatureModel, newRoot);
	}

	protected ExtendedFeatureModel(String factoryID) {
		super(factoryID);
	}

}
