package org.deltaj.transformations.cleanup.features;

import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.finder.feature.DeltaJFeaturesInFormulaFinder;
import org.deltaj.transformations.formula.DeltaJFormulaOptimizer;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJEmptyFeatureChecker {

	private final ProductLine productLine;
	private final Feature feature;

	public DeltaJEmptyFeatureChecker(Feature feature) {

		productLine = DeltaJHierarchy.getProductLine(feature);
		this.feature = feature;
	}

	public boolean isEmpty() {

		for (PartitionPart partitionPart: productLine.getPartition().getParts()) {

			for (ModuleReference moduleReference: partitionPart.getModuleReferences()) {

				if (dependsOnFeature(moduleReference)) {
					return false;
				}
			}
		}

		return true;
	}

	public void check() {

		if (!isEmpty()) {
			throw new DeltaJException("The feature '%s' is not empty.", feature.getName());
		}
	}

	private boolean dependsOnFeature(ModuleReference moduleReference) {

		PropositionalFormula when = moduleReference.getWhen();

		PropositionalFormula optimized = new DeltaJFormulaOptimizer(when).optimize();

		return new DeltaJFeaturesInFormulaFinder(optimized).find(feature);
	}
}
