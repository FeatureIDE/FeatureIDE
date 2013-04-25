package org.deltaj.transformations.evolution;

import java.util.List;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.finder.feature.references.DeltaJSpecificFeatureReferencesInFormulaFinder;

public class DeltaJFeatureInFormulaReplacer {

	private final PropositionalFormula formula;
	private final Feature feature;

	public DeltaJFeatureInFormulaReplacer(PropositionalFormula formula, Feature feature) {

		this.formula = formula;
		this.feature = feature;
	}

	public void replaceWith(Feature newFeature) {

		List<FeatureRef> references = new DeltaJSpecificFeatureReferencesInFormulaFinder(feature).find(formula);

		for (FeatureRef reference: references) {
			reference.setFeature(newFeature);
		}
	}
}
