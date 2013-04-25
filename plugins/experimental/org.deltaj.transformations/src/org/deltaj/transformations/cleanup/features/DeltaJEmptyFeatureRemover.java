package org.deltaj.transformations.cleanup.features;

import org.deltaj.deltaj.Feature;
import org.deltaj.transformations.evolution.DeltaJFeatureRemover;

public class DeltaJEmptyFeatureRemover {

	private final Feature feature;

	public DeltaJEmptyFeatureRemover(Feature feature) {

		this.feature = feature;
	}

	public void remove() {

		new DeltaJEmptyFeatureChecker(feature).check();

		new DeltaJFeatureRemover(feature).remove();
	}
}
