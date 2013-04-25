package org.deltaj.transformations.resolve;

import java.util.List;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.finder.DeltaJPrecedingActionFinder;
import org.deltaj.transformations.conditions.DeltaJActionConditionReplacer;
import org.deltaj.transformations.finder.DeltaJModuleReferenceFinder;
import org.deltaj.transformations.formula.DeltaJFormulaComparator;
import org.deltaj.transformations.modules.references.DeltaJModuleReferenceReducer;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

/**
 * This class disables all delta actions preceding a specified delta action.
 * <p>
 * Given an action <i>A</i>, which is a class, method or field removal action or
 * a method modification action. This class disables all actions, affecting the
 * same target and preceding the given action <i>A</i>, through the change of
 * their application condition. The application condition <i>C</i> of any
 * preceding action is changed to <i>C AND !R</i>, where <i>R</i> is the
 * application condition of the given removal or modification action <i>A</i>.
 * <p>
 * If necessary and only then, the preceding actions are extracted into separate
 * delta modules before their application condition is altered.
 * 
 * @author Oliver Richers
 */
class PrecedingSplActionsDisabler {

	private final IDeltaJAction deltaAction;
	private final DeltaJModuleReference actionReference;
	private final String splName;

	public PrecedingSplActionsDisabler(IDeltaJAction deltaAction, DeltaJModuleReference actionReference) {

		this.deltaAction = deltaAction;
		this.actionReference = actionReference;
		this.splName = actionReference.getSplName();
	}

	public void disable() {

		List<IDeltaJAction> precedingActions = findPrecedingActions();

		for (IDeltaJAction action: precedingActions) {

			// compute the new application condition
			PropositionalFormula newCondition = getNewApplicationCondition(action);

			// apply the new condition only if necessary
			if (!hasEqualApplicationCondition(action, newCondition)) {

				DeltaJModuleReference moduleReference = new DeltaJActionConditionReplacer(action, splName)
						.replace(newCondition);

				new DeltaJModuleReferenceReducer(moduleReference).reduce();
			}
		}
	}

	private List<IDeltaJAction> findPrecedingActions() {

		return new DeltaJPrecedingActionFinder(deltaAction, actionReference).find(deltaAction.getProgram());
	}

	private PropositionalFormula getNewApplicationCondition(IDeltaJAction action) {

		return new ResolvingFormulaBuilder(getApplicationCondition(action), actionReference.getApplicationCondition()).build();
	}

	private boolean hasEqualApplicationCondition(IDeltaJAction action, PropositionalFormula newCondition) {

		return isEqual(getApplicationCondition(action), newCondition);
	}

	private boolean isEqual(PropositionalFormula condition1, PropositionalFormula condition2) {

		return new DeltaJFormulaComparator(condition1, condition2).isEqual();
	}

	private PropositionalFormula getApplicationCondition(IDeltaJAction action) {

		return new DeltaJModuleReferenceFinder(action.getDeltaModule()).findMap().get(splName).getApplicationCondition();
	}
}
