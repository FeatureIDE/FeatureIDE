package org.deltaj.transformations.formula;

import java.util.Set;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.PropositionalFormula;

public class DeltaJFormulaComparator {

	private final PropositionalFormula formulaA;
	private final PropositionalFormula formulaB;
	private final FeatureList features;

	public static enum Result {
		// note, more result values will be added soon...
		DIFFERENT,
		EQUIVALENT;
	}

	public DeltaJFormulaComparator(PropositionalFormula formulaA, PropositionalFormula formulaB) {

		this.formulaA = formulaA;
		this.formulaB = formulaB;
		this.features = new FeatureList();

		Set<Feature> featureUnion = new FeatureSet();
		featureUnion.addAll(new DeltaJFormulaFeatureCollector().collect(formulaA));
		featureUnion.addAll(new DeltaJFormulaFeatureCollector().collect(formulaB));
		this.features.addAll(featureUnion);
	}

	public Result compare() {

		boolean equivalent = true;

		int featureCount = features.size();
		int configurationCount = 1 << featureCount;
		for (int configuration = 0; configuration < configurationCount; ++configuration) {

			Set<Feature> enabledFeatures = features.getEnabledFeaturesFor(configuration);

			boolean a = new DeltaJFormulaEvaluator(formulaA).evaluate(enabledFeatures);
			boolean b = new DeltaJFormulaEvaluator(formulaB).evaluate(enabledFeatures);

			if (a != b) {
				equivalent = false;
			}
		}

		return equivalent? Result.EQUIVALENT : Result.DIFFERENT;
	}

	public boolean isEqual() {

		return compare() == Result.EQUIVALENT;
	}

}
