package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.actions.targets.DeltaJActionTargetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJConflictingDeltaActions;
import org.deltaj.transformations.utils.logical.LogicalActionMap;

public class LogicalFieldAddition extends AbstractLogicalDeltaAction implements ILogicalSubAddition {

	private final Field fieldDefinition;

	public LogicalFieldAddition(Field field) {

		super(DeltaJActionTargetFactory.create(field));
		this.fieldDefinition = field;
	}

	public LogicalFieldAddition(FieldAddition fieldAddition) {

		super(DeltaJActionTargetFactory.create(fieldAddition));
		this.fieldDefinition = fieldAddition.getField();
	}

	public Field getFieldDefinition() {

		return fieldDefinition;
	}

	@Override
	public void addTo(ClassAddition classAddition) {

		classAddition.getClass_().getFields().add(fieldDefinition);
	}

	@Override
	public void addTo(ClassModification classModification) {

		FieldAddition fieldAddition = DeltajFactory.eINSTANCE.createFieldAddition();
		fieldAddition.setField(fieldDefinition);
		classModification.getSubActions().add(fieldAddition);
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
			inverseActions.add(new LogicalFieldRemoval(target));
		} else {
			throw new DeltaJConflictingDeltaActions(targetAction, this);
		}
	}
}