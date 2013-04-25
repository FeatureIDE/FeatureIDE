package org.deltaj.transformations.cleanup.features;

import org.deltaj.deltaj.Feature;
import org.deltaj.transformations.evolution.DeltaJFeaturesMerger;

public class DeltaJDuplicatedFeaturesMerger {

	private final Feature featureA;
	private final Feature featureB;
	private final String mergedName;

	public DeltaJDuplicatedFeaturesMerger(Feature featureA, Feature featureB, String mergedName) {

		this.featureA = featureA;
		this.featureB = featureB;
		this.mergedName = mergedName;
	}

	public void merge() {

		new DeltaJDuplicatedFeaturesChecker(featureA, featureB).check();

		new DeltaJFeaturesMerger(featureA, featureB, mergedName).merge();
	}
}
