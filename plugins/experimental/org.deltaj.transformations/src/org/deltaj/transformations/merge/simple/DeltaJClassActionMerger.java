package org.deltaj.transformations.merge.simple;

import java.util.Collection;
import java.util.List;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.IDeltaJClassAction;
import org.deltaj.transformations.utils.ListFactory;
import org.deltaj.transformations.utils.ListUtils;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

/**
 * Merges a list of class actions into a single class actions.
 * <p>
 * Currently only {@link ClassModification} actions are supported.
 * 
 * @author Oliver Richers
 */
public class DeltaJClassActionMerger {

	private final List<IDeltaJClassAction> classActions;

	public DeltaJClassActionMerger(Collection<IDeltaJClassAction> actions) {

		// copying list to avoid potential side-effects
		this.classActions = ListFactory.createArrayList(actions);

		validateActionCount();
		validateTypeOfActions();
	}

	private void validateActionCount() {

		if (classActions.size() < 2) {
			throw new DeltaJException("At least 2 class actions are required.");
		}
	}

	private void validateTypeOfActions() {

		for (IDeltaJClassAction classAction: classActions) {

			if (classAction.getActionType() != DeltaJActionType.MODIFICATION) {
				throw new DeltaJException("Currently only class modification actions are supported.");
			}
		}
	}

	public void merge() {

		IDeltaJClassAction firstAction = classActions.get(0);

		for (IDeltaJClassAction classAction: ListUtils.subList(classActions, 1)) {
			mergeSubActions(firstAction, classAction);
			removeClassAction(classAction);
		}
	}

	private void mergeSubActions(IDeltaJClassAction destinationAction, IDeltaJClassAction classAction) {

		ClassModification destinationStatement = (ClassModification) destinationAction.getActionStatement();
		ClassModification actionStatement = (ClassModification) classAction.getActionStatement();

		// copying list to avoid side-effects
		List<DeltaSubAction> subActions = ListFactory.createArrayList(actionStatement.getSubActions());
		for (DeltaSubAction subAction: subActions) {
			destinationStatement.getSubActions().add(subAction);
		}
	}

	private void removeClassAction(IDeltaJClassAction classAction) {

		ListUtils.removeElementByIdentity(classAction.getDeltaModule().getDeltaActions(), classAction.getActionStatement());
	}
}
