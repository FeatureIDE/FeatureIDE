package org.deltaj.transformations.resolve;

import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.formula.DeltaJFormulaBuilder;

class ResolvingFormulaBuilder extends DeltaJFormulaBuilder {

	private final PropositionalFormula actionCondition;
	private final PropositionalFormula removalCondition;

	public ResolvingFormulaBuilder(PropositionalFormula actionCondition, PropositionalFormula removalCondition) {

		this.actionCondition = actionCondition != null? actionCondition : createTrue();
		this.removalCondition = removalCondition != null? removalCondition : createTrue();
	}

	public PropositionalFormula build() {

		// copy conditions and return build formula 'a && !r' 
		return optimize(and(copy(actionCondition), not(copy(removalCondition))));
	}
}
