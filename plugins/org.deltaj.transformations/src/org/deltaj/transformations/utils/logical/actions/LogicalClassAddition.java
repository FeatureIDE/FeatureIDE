package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.ClassAddition;
import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.actions.targets.DeltaJActionTargetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJConflictingDeltaActions;
import org.deltaj.transformations.utils.logical.LogicalActionMap;

public class LogicalClassAddition extends AbstractLogicalDeltaAction implements ILogicalClassAction {

	private final Class classDefinition;

	public LogicalClassAddition(ClassAddition classAddition) {

		super(DeltaJActionTargetFactory.create(classAddition));
		this.classDefinition = classAddition.getClass_();
	}

	public Class getClassDefinition() {

		return classDefinition;
	}

	private String getClassName() {

		return getClassDefinition().getExtends();
	}

	private String getExtendsName() {

		return getClassDefinition().getExtends();
	}

	private boolean isEquivaletTo(LogicalClassAddition otherAddition) {

		return getClassName().equals(otherAddition.getClassName())
				&& getExtendsName().equals(otherAddition.getExtendsName());
	}

	@Override
	public DeltaJActionType getActionType() {

		return DeltaJActionType.ADDITION;
	}

	@Override
	public void applyWithInverse(LogicalActionMap targetActions, LogicalActionMap inverseActions) {

		DeltaJActionTarget target = getTarget();
		ILogicalAction targetAction = targetActions.get(target);

		if (targetAction == null || isRemoval(targetAction)) {
			targetActions.add(this);
			inverseActions.add(new LogicalClassRemoval(target));
		} else if (isCompatibleAddition(targetAction)) {
			// can be ignored
		} else {
			throw new DeltaJConflictingDeltaActions(targetAction, this);
		}
	}

	private boolean isCompatibleAddition(ILogicalAction targetAction) {

		if (targetAction.getActionType() == DeltaJActionType.ADDITION) {
			return isEquivaletTo((LogicalClassAddition) targetAction);
		}

		return false;
	}
}
