package org.deltaj.transformations.finder.feature;

import java.util.List;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.finder.feature.references.DeltaJFeatureReferencesInFormulaFinder;
import org.deltaj.transformations.formula.FeatureSet;

public class DeltaJFeaturesInFormulaFinder {

	private final PropositionalFormula formula;

	public DeltaJFeaturesInFormulaFinder(PropositionalFormula formula) {

		this.formula = formula;
	}

	public FeatureSet find() {

		FeatureSet featureSet = new FeatureSet();

		List<FeatureRef> references = new DeltaJFeatureReferencesInFormulaFinder(formula).find();
		for (FeatureRef reference: references) {
			featureSet.add(reference.getFeature());
		}

		return featureSet;
	}

	public boolean find(Feature feature) {

		return find().contains(feature);
	}
}
