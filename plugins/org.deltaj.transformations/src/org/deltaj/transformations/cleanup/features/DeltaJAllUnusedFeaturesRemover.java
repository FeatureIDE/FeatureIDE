package org.deltaj.transformations.cleanup.features;

import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Features;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.evolution.DeltaJFeatureRemover;
import org.deltaj.transformations.finder.feature.DeltaJUnusedFeaturesFinder;
import org.deltaj.transformations.utils.DeltaJHierarchy;

public class DeltaJAllUnusedFeaturesRemover {

	public void remove(Program program) {

		for (Feature feature: new DeltaJUnusedFeaturesFinder().find(program)) {
			new DeltaJFeatureRemover(feature).remove();
		}
	}

	public void remove(ProductLine productLine) {

		for (Feature feature: new DeltaJUnusedFeaturesFinder().find(productLine)) {
			new DeltaJFeatureRemover(feature).remove();
		}
	}

	public void remove(Features features) {

		remove(DeltaJHierarchy.getProductLine(features));
	}
}
