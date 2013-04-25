package org.deltaj.transformations.cleanup.features;

import org.deltaj.deltaj.Feature;
import org.deltaj.transformations.evolution.DeltaJFeatureRemover;

public class DeltaJUnusedFeatureRemover {

	private final Feature feature;

	public DeltaJUnusedFeatureRemover(Feature feature) {

		this.feature = feature;
	}

	public void remove() {

		new DeltaJUnusedFeatureChecker(feature).check();

		new DeltaJFeatureRemover(feature).remove();
	}
}
