package org.deltaj.transformations.cleanup.features;

import java.util.Set;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.finder.feature.DeltaJUnusedFeaturesFinder;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJUnusedFeatureChecker {

	private final Feature feature;

	public DeltaJUnusedFeatureChecker(Feature feature) {

		this.feature = feature;
	}

	public boolean isUnused() {

		ProductLine productLine = DeltaJHierarchy.getProductLine(feature);

		return getUnusedFeatures(productLine).contains(feature);
	}

	public void check() {

		if (!isUnused()) {
			throw new DeltaJException("The feature '%s' is not unused.", feature.getName());
		}
	}

	private Set<Feature> getUnusedFeatures(ProductLine productLine) {

		return new DeltaJUnusedFeaturesFinder().find(productLine);
	}
}
