package org.deltaj.transformations.formula;

import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.formula.logic.LogicFormula;

public class DeltaJFormulaOptimizer {

	private final PropositionalFormula formula;

	public DeltaJFormulaOptimizer(PropositionalFormula formula) {

		this.formula = formula;
	}

	public PropositionalFormula optimize() {

		DeltaJFormulaToLogicFormulaConverter converter = new DeltaJFormulaToLogicFormulaConverter(formula);

		LogicFormula logicFormula = converter.convert();

		LogicFormula optimizedFormula = logicFormula.minimize();

		return new DeltaJLogicFormulaToFormulaConverter(optimizedFormula, converter.getFeatures()).convert();
	}
}
