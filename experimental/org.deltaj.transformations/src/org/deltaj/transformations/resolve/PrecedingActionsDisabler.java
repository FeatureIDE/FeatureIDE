package org.deltaj.transformations.resolve;

import java.util.Collection;
import org.deltaj.transformations.actions.IDeltaJAction;
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
class PrecedingActionsDisabler {

	private final IDeltaJAction deltaAction;

	public PrecedingActionsDisabler(IDeltaJAction deltaAction) {

		this.deltaAction = deltaAction;
	}

	public void disable() {

		Collection<DeltaJModuleReference> actionReferences = findActionReferences();

		for (DeltaJModuleReference actionReference: actionReferences) {
			disablePrecedingActions(actionReference);
		}
	}

	private Collection<DeltaJModuleReference> findActionReferences() {

		return deltaAction.findModuleReferences().values();
	}

	private void disablePrecedingActions(DeltaJModuleReference actionReference) {

		new PrecedingSplActionsDisabler(deltaAction, actionReference).disable();
	}
}
