package org.deltaj.transformations.evolution;

import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;
import org.deltaj.transformations.utils.ListUtils;

public class DeltaJFeatureFromProductRemover {

	private final Product product;
	private final Feature feature;

	public DeltaJFeatureFromProductRemover(Product product, Feature feature) {

		this.product = product;
		this.feature = feature;
	}

	public void remove() {

		ListUtils.removeElementByIdentity(product.getFeatures(), feature);
	}
}
