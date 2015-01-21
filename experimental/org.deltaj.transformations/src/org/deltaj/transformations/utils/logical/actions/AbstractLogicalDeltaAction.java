package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;

public abstract class AbstractLogicalDeltaAction implements ILogicalAction {

	private final DeltaJActionTarget actionTarget;

	protected AbstractLogicalDeltaAction(DeltaJActionTarget actionTarget) {

		this.actionTarget = actionTarget;
	}

	@Override
	public String getFullTargetName() {

		return actionTarget.getFullName();
	}

	@Override
	public DeltaJActionTarget getTarget() {

		return actionTarget;
	}

	protected static boolean isAddition(ILogicalAction action) {

		return action != null && action.getActionType() == DeltaJActionType.ADDITION;
	}

	protected static boolean isModification(ILogicalAction action) {

		return action != null && action.getActionType() == DeltaJActionType.MODIFICATION;
	}

	protected static boolean isRemoval(ILogicalAction action) {

		return action != null && action.getActionType() == DeltaJActionType.REMOVAL;
	}
}
