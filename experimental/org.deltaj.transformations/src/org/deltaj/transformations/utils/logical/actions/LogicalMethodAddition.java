package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.actions.targets.DeltaJActionTargetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJConflictingDeltaActions;
import org.deltaj.transformations.utils.logical.LogicalActionMap;

public class LogicalMethodAddition extends AbstractLogicalDeltaAction implements ILogicalSubAddition {

	private final Method methodDefinition;

	public LogicalMethodAddition(DeltaJActionTarget target, Method methodDefinition) {

		super(target);
		this.methodDefinition = methodDefinition;
	}

	public LogicalMethodAddition(Method methodDefinition) {

		super(DeltaJActionTargetFactory.create(methodDefinition));
		this.methodDefinition = methodDefinition;
	}

	public LogicalMethodAddition(MethodAddition methodAddition) {

		super(DeltaJActionTargetFactory.create(methodAddition));
		this.methodDefinition = methodAddition.getMethod();
	}

	public Method getMethodDefinition() {

		return methodDefinition;
	}

	@Override
	public void addTo(ClassAddition classAddition) {

		classAddition.getClass_().getMethods().add(methodDefinition);
	}

	@Override
	public void addTo(ClassModification classModification) {

		MethodAddition methodAddition = DeltajFactory.eINSTANCE.createMethodAddition();
		methodAddition.setMethod(methodDefinition);
		classModification.getSubActions().add(methodAddition);
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
			inverseActions.add(new LogicalMethodRemoval(target));
		} else {
			throw new DeltaJConflictingDeltaActions(targetAction, this);
		}
	}
}
