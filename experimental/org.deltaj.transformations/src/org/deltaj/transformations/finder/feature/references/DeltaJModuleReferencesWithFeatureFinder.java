package org.deltaj.transformations.finder.feature.references;

import java.util.List;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListFactory;

public class DeltaJModuleReferencesWithFeatureFinder {

	private final ProductLine productLine;
	private final Feature feature;
	private final List<ModuleReference> moduleReferences;

	public DeltaJModuleReferencesWithFeatureFinder(Feature feature) {

		this.productLine = DeltaJHierarchy.getProductLine(DeltaJHierarchy.getFeatures(feature));
		this.feature = feature;
		this.moduleReferences = ListFactory.createArrayList();
	}

	public List<ModuleReference> find() {

		moduleReferences.clear();

		for (PartitionPart deltaSpecification: productLine.getPartition().getParts()) {
			for (ModuleReference moduleReference: deltaSpecification.getModuleReferences()) {

				PropositionalFormula formula = moduleReference.getWhen();

				if (!new DeltaJSpecificFeatureReferencesInFormulaFinder(feature).find(formula).isEmpty()) {
					moduleReferences.add(moduleReference);
				}
			}
		}

		return moduleReferences;
	}
}
