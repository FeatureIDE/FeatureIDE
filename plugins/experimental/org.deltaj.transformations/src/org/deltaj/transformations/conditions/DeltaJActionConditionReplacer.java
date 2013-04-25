package org.deltaj.transformations.conditions;

import java.util.Map;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.extract.DeltaJActionExtractor;
import org.deltaj.transformations.finder.DeltaJModuleReferenceFinder;
import org.deltaj.transformations.formula.DeltaJFormulaOptimizer;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

/**
 * Replaces the application condition of a delta action.
 * <p>
 * If necessary the action is extracted from the delta module before changing
 * the application condition, to not affect other parts of the delta module.
 * 
 * @author Oliver Richers
 */
public class DeltaJActionConditionReplacer {

	private final IDeltaJAction action;
	private final String splName;

	public DeltaJActionConditionReplacer(IDeltaJAction action, String splName) {

		this.action = action;
		this.splName = splName;
	}

	public DeltaJModuleReference replace(PropositionalFormula newCondition) {

		// first, the action is extracted into a separate module if necessary
		DeltaJModuleReference moduleReference = extractActionIfNecessary();

		// now, the application condition can be replaced
		replace(moduleReference, newCondition);

		return moduleReference;
	}

	private DeltaJModuleReference extractActionIfNecessary() {

		DeltaModule actionModule = new DeltaJActionExtractor(action).extractIfNecessary();
		return getModuleReference(actionModule);
	}

	private DeltaJModuleReference getModuleReference(DeltaModule module) {

		Map<String, DeltaJModuleReference> references = new DeltaJModuleReferenceFinder(module).findMap();
		return references.get(splName);
	}

	private void replace(DeltaJModuleReference moduleReference, PropositionalFormula newCondition) {

		moduleReference.getStatement().setWhen(new DeltaJFormulaOptimizer(newCondition).optimize());
	}
}
