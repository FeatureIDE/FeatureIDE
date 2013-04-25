package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.actions.targets.DeltaJActionTargetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.deltaj.transformations.utils.logical.LogicalActionMap;

public class LogicalMethodRemoval extends AbstractLogicalDeltaAction implements ILogicalSubRemoval {

	public LogicalMethodRemoval(DeltaJActionTarget target) {

		super(target);
	}

	public LogicalMethodRemoval(MethodRemoval methodRemoval) {

		super(DeltaJActionTargetFactory.create(methodRemoval));
	}

	@Override
	public void addTo(ClassModification classModification) {

		MethodRemoval methodRemoval = DeltajFactory.eINSTANCE.createMethodRemoval();
		methodRemoval.setName(getTarget().getSubName());
		classModification.getSubActions().add(methodRemoval);
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
		} else if (isModification(targetAction)) {
			LogicalMethodModification methodModification = (LogicalMethodModification) targetAction;
			targetActions.remove(target);
			inverseActions.add(new LogicalMethodAddition(target, methodModification.getMethodDefinition()));
		} else {
			throw new DeltaJException(
					"No matching method addition or modification action found for removal of '%s'.",
					target.getFullName());
		}
	}
}