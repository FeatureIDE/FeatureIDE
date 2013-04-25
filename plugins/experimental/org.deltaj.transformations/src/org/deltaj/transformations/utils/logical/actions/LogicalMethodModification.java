package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.actions.targets.DeltaJActionTargetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.deltaj.transformations.utils.logical.LogicalActionMap;

public class LogicalMethodModification extends AbstractLogicalDeltaAction implements ILogicalSubAction {

	private final Method methodDefinition;

	public LogicalMethodModification(DeltaJActionTarget target, Method methodDefinition) {

		super(target);
		this.methodDefinition = methodDefinition;
	}

	public LogicalMethodModification(MethodModification methodModification) {

		super(DeltaJActionTargetFactory.create(methodModification));
		this.methodDefinition = methodModification.getMethod();
	}

	public Method getMethodDefinition() {

		return methodDefinition;
	}

	@Override
	public void addTo(ClassModification classModification) {

		MethodModification methodModification = DeltajFactory.eINSTANCE.createMethodModification();
		methodModification.setMethod(methodDefinition);
		classModification.getSubActions().add(methodModification);
	}

	@Override
	public DeltaJActionType getActionType() {

		return DeltaJActionType.MODIFICATION;
	}

	@Override
	public void applyWithInverse(LogicalActionMap targetActions, LogicalActionMap inverseActions) {

		DeltaJActionTarget target = getTarget();
		ILogicalAction targetAction = targetActions.get(target);

		if (isAddition(targetAction)) {
			LogicalMethodAddition methodAddition = (LogicalMethodAddition) targetAction;
			targetActions.add(new LogicalMethodAddition(target, methodDefinition));
			inverseActions.add(new LogicalMethodModification(target, methodAddition.getMethodDefinition()));
		} else if (isModification(targetAction)) {
			targetActions.add(this);
			inverseActions.add(targetAction);
		} else {
			throw new DeltaJException(
					"No matching method addition or modification action found for modification of '%s'.",
					target.getFullName());
		}
	}
}
