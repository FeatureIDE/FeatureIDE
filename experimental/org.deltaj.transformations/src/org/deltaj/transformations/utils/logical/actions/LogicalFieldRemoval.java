package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.actions.targets.DeltaJActionTargetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.deltaj.transformations.utils.logical.LogicalActionMap;

public class LogicalFieldRemoval extends AbstractLogicalDeltaAction implements ILogicalSubRemoval {

	public LogicalFieldRemoval(DeltaJActionTarget target) {

		super(target);
	}

	public LogicalFieldRemoval(FieldRemoval fieldRemoval) {

		super(DeltaJActionTargetFactory.create(fieldRemoval));
	}

	@Override
	public void addTo(ClassModification classModification) {

		FieldRemoval fieldRemoval = DeltajFactory.eINSTANCE.createFieldRemoval();
		fieldRemoval.setName(getTarget().getSubName());
		classModification.getSubActions().add(fieldRemoval);
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
					"No matching field addition action found for removal of '%s'.",
					target.getFullName());
		}
	}
}