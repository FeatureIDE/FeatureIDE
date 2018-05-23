package org.deltaj.transformations.finder.feature.references;

import java.util.List;
import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListFactory;

public class DeltaJFeatureReferencesFinder {

	private final ProductLine productLine;
	private final Feature feature;
	private final List<FeatureRef> featureReferences;

	public DeltaJFeatureReferencesFinder(Feature feature) {

		this.productLine = DeltaJHierarchy.getProductLine(feature);
		this.feature = feature;
		this.featureReferences = ListFactory.createArrayList();
	}

	public List<FeatureRef> find() {

		featureReferences.clear();

		collectReferencesInConfigurations();
		collectReferencesInConditions();

		return featureReferences;
	}

	private void collectReferencesInConfigurations() {

		for (Configuration configuration: productLine.getConfigurations().getConfigurations()) {
			PropositionalFormula formula = configuration.getFormula();
			featureReferences.addAll(new DeltaJSpecificFeatureReferencesInFormulaFinder(feature).find(formula));
		}

	}

	private void collectReferencesInConditions() {

		for (PartitionPart partitionPart: productLine.getPartition().getParts()) {

			for (ModuleReference moduleReference: partitionPart.getModuleReferences()) {
				PropositionalFormula formula = moduleReference.getWhen();
				featureReferences.addAll(new DeltaJSpecificFeatureReferencesInFormulaFinder(feature).find(formula));
			}
		}
	}
}
