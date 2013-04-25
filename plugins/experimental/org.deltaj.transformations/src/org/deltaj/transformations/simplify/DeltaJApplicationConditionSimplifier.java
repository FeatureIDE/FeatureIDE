package org.deltaj.transformations.simplify;

import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.formula.DeltaJFormulaOptimizer;
import org.deltaj.transformations.modules.references.DeltaJModuleReferenceImpl;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

public class DeltaJApplicationConditionSimplifier {

	private final DeltaJModuleReference moduleReference;

	public DeltaJApplicationConditionSimplifier(ModuleReference moduleReference) {

		this(DeltaJModuleReferenceImpl.get(moduleReference));
	}

	public DeltaJApplicationConditionSimplifier(DeltaJModuleReference moduleReference) {

		this.moduleReference = moduleReference;
	}

	public void simplify() {

		PropositionalFormula when = moduleReference.getStatement().getWhen();
		if (when != null) {
			when = new DeltaJFormulaOptimizer(when).optimize();
			moduleReference.getStatement().setWhen(when);
		}
	}
}
