package org.deltaj.transformations.simplify;

import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.formula.DeltaJFormulaOptimizer;

public class DeltaJFeatureConfigurationSimplifier {

	private final Configuration configuration;

	public DeltaJFeatureConfigurationSimplifier(Configuration configuration) {

		this.configuration = configuration;
	}

	public void simplify() {

		PropositionalFormula formula = configuration.getFormula();
		if (formula != null) {
			formula = new DeltaJFormulaOptimizer(formula).optimize();
			configuration.setFormula(formula);
		}
	}
}
