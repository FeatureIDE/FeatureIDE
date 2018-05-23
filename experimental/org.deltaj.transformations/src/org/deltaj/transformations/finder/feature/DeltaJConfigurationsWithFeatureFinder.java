package org.deltaj.transformations.finder.feature;

import java.util.List;
import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.finder.feature.references.DeltaJSpecificFeatureReferencesInFormulaFinder;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListFactory;

public class DeltaJConfigurationsWithFeatureFinder {

	private final ProductLine productLine;
	private final Feature feature;
	private final List<Configuration> configurations;

	public DeltaJConfigurationsWithFeatureFinder(Feature feature) {

		this.productLine = DeltaJHierarchy.getProductLine(DeltaJHierarchy.getFeatures(feature));
		this.feature = feature;
		this.configurations = ListFactory.createArrayList();
	}

	public List<Configuration> find() {

		configurations.clear();

		for (Configuration configuration: productLine.getConfigurations().getConfigurations()) {

			PropositionalFormula formula = configuration.getFormula();

			if (!new DeltaJSpecificFeatureReferencesInFormulaFinder(feature).find(formula).isEmpty()) {
				configurations.add(configuration);
			}
		}

		return configurations;
	}
}
