package org.deltaj.transformations.formula;

import java.util.List;
import java.util.Set;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.formula.logic.LogicFormula;

public class DeltaJFormulaToLogicFormulaConverter {

	private final DeltaJFormulaEvaluator evaluator;
	private final FeatureList features;

	public DeltaJFormulaToLogicFormulaConverter(PropositionalFormula formula) {

		this.evaluator = new DeltaJFormulaEvaluator(formula);
		this.features = new FeatureList();

		features.addAll(new DeltaJFormulaFeatureCollector().collect(formula));
	}

	public LogicFormula convert() {

		int featureCount = features.size();

		if (featureCount == 0) {
			return new LogicFormula(evaluator.evaluate());
		} else {
			return convertFormula(featureCount);
		}
	}

	private LogicFormula convertFormula(int featureCount) {

		LogicFormula logicFormula = new LogicFormula(featureCount);

		int configurationCount = 1 << featureCount;
		for (int configuration = 0; configuration < configurationCount; ++configuration) {
			checkConfiguration(logicFormula, configuration);
		}

		return logicFormula.getTerms().isEmpty()? new LogicFormula(false) : logicFormula;
	}

	private void checkConfiguration(LogicFormula logicFormula, int configuration) {

		Set<Feature> enabledFeatures = getEnabledFeatures(configuration);

		boolean result = evaluator.evaluate(enabledFeatures);

		if (result) {
			logicFormula.addTerm(configuration);
		}
	}

	private Set<Feature> getEnabledFeatures(int configuration) {

		return features.getEnabledFeaturesFor(configuration);
	}

	public List<Feature> getFeatures() {

		return features;
	}
}
