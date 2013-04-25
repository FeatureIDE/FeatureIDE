package org.deltaj.transformations.evolution;

import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListUtils;

public class DeltaJFeatureFromFeatureSetRemover {

	private final ProductLine productLine;
	private final Feature feature;

	public DeltaJFeatureFromFeatureSetRemover(Feature feature) {

		this.productLine = DeltaJHierarchy.getProductLine(feature);
		this.feature = feature;
	}

	public void remove() {

		ListUtils.removeElementByIdentity(productLine.getFeatures().getFeaturesList(), feature);
	}
}
