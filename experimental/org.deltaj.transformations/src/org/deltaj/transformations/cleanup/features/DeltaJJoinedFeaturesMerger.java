package org.deltaj.transformations.cleanup.features;

import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.checks.DeltaJSameProductLineChecker;
import org.deltaj.transformations.evolution.DeltaJFeatureFromProductRemover;
import org.deltaj.transformations.evolution.DeltaJFeaturesMerger;
import org.deltaj.transformations.finder.product.DeltaJProductsOfProductLineFinder;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListUtils;

public class DeltaJJoinedFeaturesMerger {

	private final Feature featureA;
	private final Feature featureB;
	private final String mergedName;
	private final ProductLine productLine;

	public DeltaJJoinedFeaturesMerger(Feature featureA, Feature featureB, String mergedName) {

		this.productLine = DeltaJHierarchy.getProductLine(featureA);
		this.featureA = featureA;
		this.featureB = featureB;
		this.mergedName = mergedName;
	}

	public void merge() {

		new DeltaJSameProductLineChecker().check(featureA, featureB);

		new DeltaJJoinedFeaturesChecker(featureA, featureB).check();

		removeSingleInstancesFromProducts();

		new DeltaJFeaturesMerger(featureA, featureB, mergedName).merge();
	}

	private void removeSingleInstancesFromProducts() {

		for (Product product: new DeltaJProductsOfProductLineFinder(productLine).find()) {
			removeSingleInstancesFromProduct(product);
		}
	}

	private void removeSingleInstancesFromProduct(Product product) {

		boolean containsA = ListUtils.containsByIdentity(product.getFeatures(), featureA);
		boolean containsB = ListUtils.containsByIdentity(product.getFeatures(), featureB);

		if (containsA && !containsB) {
			new DeltaJFeatureFromProductRemover(product, featureA).remove();
		}

		if (containsB && !containsA) {
			new DeltaJFeatureFromProductRemover(product, featureB).remove();
		}
	}
}
