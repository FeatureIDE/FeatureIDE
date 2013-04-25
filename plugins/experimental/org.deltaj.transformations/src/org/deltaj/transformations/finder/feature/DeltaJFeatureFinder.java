package org.deltaj.transformations.finder.feature;

import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.ProductLine;

public class DeltaJFeatureFinder {

	private final ProductLine productLine;
	private final String featureName;

	public DeltaJFeatureFinder(ProductLine productLine, String featureName) {

		this.productLine = productLine;
		this.featureName = featureName;
	}

	public Feature find() {

		for (Feature feature: productLine.getFeatures().getFeaturesList()) {

			if (feature.getName().equals(featureName)) {
				return feature;
			}
		}

		return null;
	}
}
