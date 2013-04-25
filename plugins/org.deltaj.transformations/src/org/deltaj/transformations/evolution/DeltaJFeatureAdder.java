package org.deltaj.transformations.evolution;

import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.finder.feature.DeltaJFeatureFinder;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJFeatureAdder {

	private final ProductLine productLine;
	private final String featureName;

	public DeltaJFeatureAdder(ProductLine productLine, String featureName) {

		this.productLine = productLine;
		this.featureName = featureName;
	}

	public Feature add() {

		checkName();

		Feature feature = createFeature();

		addToProductLine(feature);

		return feature;
	}

	private void checkName() {

		if (new DeltaJFeatureFinder(productLine, featureName).find() != null) {
			throw new DeltaJException("A feature with the name '%s' already exists.", featureName);
		}
	}

	private Feature createFeature() {

		Feature feature = DeltajFactory.eINSTANCE.createFeature();

		feature.setName(featureName);

		return feature;
	}

	private void addToProductLine(Feature feature) {

		productLine.getFeatures().getFeaturesList().add(feature);
	}
}
