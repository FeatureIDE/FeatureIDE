package org.deltaj.transformations.evolution;

import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.checks.DeltaJSameProductLineChecker;
import org.deltaj.transformations.finder.product.DeltaJProductsOfProductLineFinder;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListUtils;

public class DeltaJFeaturesMerger {

	private final ProductLine productLine;
	private final Feature featureA;
	private final Feature featureB;
	private final String mergedName;
	private Feature mergedFeature;

	public DeltaJFeaturesMerger(Feature featureA, Feature featureB, String mergedName) {

		this.productLine = DeltaJHierarchy.getProductLine(featureA);
		this.featureA = featureA;
		this.featureB = featureB;
		this.mergedName = mergedName;
	}

	public void merge() {

		new DeltaJSameProductLineChecker().check(featureA, featureB);

		addMergedFeature();
		replaceReferencesInConfigurations();
		replaceReferencesInConditions();
		replaceReferencesInProducts();
		removeOriginalFeatures();
	}

	private void addMergedFeature() {

		mergedFeature = new DeltaJFeatureAdder(productLine, mergedName).add();
	}

	private void replaceReferencesInConfigurations() {

		for (Configuration configuration: productLine.getConfigurations().getConfigurations()) {

			replaceReferences(configuration.getFormula());
		}
	}

	private void replaceReferencesInConditions() {

		for (PartitionPart partitionPart: productLine.getPartition().getParts()) {
			for (ModuleReference moduleReference: partitionPart.getModuleReferences()) {

				replaceReferences(moduleReference.getWhen());
			}
		}
	}

	private void replaceReferences(PropositionalFormula formula) {

		new DeltaJFeatureInFormulaReplacer(formula, featureA).replaceWith(mergedFeature);
		new DeltaJFeatureInFormulaReplacer(formula, featureB).replaceWith(mergedFeature);
	}

	private void replaceReferencesInProducts() {

		for (Product product: new DeltaJProductsOfProductLineFinder(productLine).find()) {
			replaceReferences(product);
		}
	}

	private void replaceReferences(Product product) {

		boolean containsA = ListUtils.containsByIdentity(product.getFeatures(), featureA);
		boolean containsB = ListUtils.containsByIdentity(product.getFeatures(), featureB);

		if (containsA || containsB) {
			new DeltaJFeatureFromProductRemover(product, featureA).remove();
			new DeltaJFeatureFromProductRemover(product, featureB).remove();
			new DeltaJFeatureToProductAdder(product, mergedFeature).add();
		}
	}

	private void removeOriginalFeatures() {

		new DeltaJFeatureFromFeatureSetRemover(featureA).remove();
		new DeltaJFeatureFromFeatureSetRemover(featureB).remove();
	}
}
