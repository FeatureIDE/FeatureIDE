package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.actions.targets.DeltaJActionTargetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.deltaj.transformations.utils.logical.LogicalActionMap;

public class LogicalClassRemoval extends AbstractLogicalDeltaAction implements ILogicalClassAction {

	public LogicalClassRemoval(DeltaJActionTarget actionTarget) {

		super(actionTarget);
	}

	public LogicalClassRemoval(ClassRemoval classRemoval) {

		super(DeltaJActionTargetFactory.create(classRemoval));
	}

	@Override
	public DeltaJActionType getActionType() {

		return DeltaJActionType.REMOVAL;
	}

	@Override
	public void applyWithInverse(LogicalActionMap targetActions, LogicalActionMap inverseActions) {

		DeltaJActionTarget target = getTarget();
		ILogicalAction targetAction = targetActions.get(target);

		if (isAddition(targetAction)) {
			targetActions.remove(target);
			inverseActions.add(targetAction);
		} else {
			throw new DeltaJException(
					"No matching class addition action found for removal of '%s'.",
					target.getFullName());
		}
	}
}