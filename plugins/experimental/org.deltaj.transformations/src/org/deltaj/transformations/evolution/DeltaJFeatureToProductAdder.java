package org.deltaj.transformations.evolution;

import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;

public class DeltaJFeatureToProductAdder {

	private final Product product;
	private final Feature feature;

	public DeltaJFeatureToProductAdder(Product product, Feature feature) {

		this.product = product;
		this.feature = feature;
	}

	public void add() {

		product.getFeatures().add(feature);
	}
}
