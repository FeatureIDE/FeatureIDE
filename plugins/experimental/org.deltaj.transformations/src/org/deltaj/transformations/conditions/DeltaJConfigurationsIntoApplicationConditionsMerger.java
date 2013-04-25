package org.deltaj.transformations.conditions;

import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.Configurations;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.formula.DeltaJFormulaBuilder;
import org.deltaj.transformations.modules.references.DeltaJModuleReferenceImpl;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

public class DeltaJConfigurationsIntoApplicationConditionsMerger {

	private final DeltaJFormulaBuilder formulaBuilder;
	private final DeltaJModuleReference moduleReference;
	private PropositionalFormula when;

	public DeltaJConfigurationsIntoApplicationConditionsMerger(ModuleReference moduleReference) {

		this(DeltaJModuleReferenceImpl.get(moduleReference));
	}

	public DeltaJConfigurationsIntoApplicationConditionsMerger(DeltaJModuleReference moduleReference) {

		this.formulaBuilder = new DeltaJFormulaBuilder();
		this.moduleReference = moduleReference;
		this.when = moduleReference.getStatement().getWhen();
	}

	public void merge() {

		Configurations configurations = moduleReference.getSplSpecification().getConfigurations();
		for (Configuration configuration: configurations.getConfigurations()) {
			merge(configuration);
		}
		moduleReference.getStatement().setWhen(when);
	}

	private void merge(Configuration configuration) {

		PropositionalFormula formula = formulaBuilder.copy(configuration.getFormula());

		when = formulaBuilder.and(when, formula);
	}
}
