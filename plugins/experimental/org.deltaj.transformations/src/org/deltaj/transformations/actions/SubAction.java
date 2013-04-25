package org.deltaj.transformations.actions;

import java.util.Map;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.transformations.exceptions.DeltaJInvalidActionType;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

class SubAction implements IDeltaJClassSubAction {

	private final DeltaSubAction actionStatement;
	private final DeltaJActionType actionType;
	private final DeltaJActionTargetType targetType;
	private final String targetName;

	protected SubAction(DeltaSubAction actionStatement) {

		this.actionStatement = actionStatement;
		this.actionType = determineType();
		this.targetType = determineTargetType();
		this.targetName = determineTargetName();
	}

	private DeltaJActionType determineType() {

		if (actionStatement instanceof MethodAddition || actionStatement instanceof FieldAddition) {
			return DeltaJActionType.ADDITION;
		} else if (actionStatement instanceof MethodRemoval || actionStatement instanceof FieldRemoval) {
			return DeltaJActionType.REMOVAL;
		} else if (actionStatement instanceof MethodModification) {
			return DeltaJActionType.MODIFICATION;
		} else {
			throw new DeltaJInvalidActionType(actionStatement);
		}
	}

	private DeltaJActionTargetType determineTargetType() {

		if (actionStatement instanceof MethodAddition || actionStatement instanceof MethodRemoval
				|| actionStatement instanceof MethodModification) {
			return DeltaJActionTargetType.METHOD;
		} else if (actionStatement instanceof FieldAddition || actionStatement instanceof FieldRemoval) {
			return DeltaJActionTargetType.FIELD;
		} else {
			throw new IllegalArgumentException("Invalid delta action type: " + actionStatement.getClass().getName());
		}
	}

	private String determineTargetName() {

		if (actionStatement instanceof MethodAddition) {
			return ((MethodAddition) actionStatement).getMethod().getName();
		} else if (actionStatement instanceof MethodRemoval) {
			return ((MethodRemoval) actionStatement).getName();
		} else if (actionStatement instanceof MethodModification) {
			return ((MethodModification) actionStatement).getMethod().getName();
		} else if (actionStatement instanceof FieldAddition) {
			return ((FieldAddition) actionStatement).getField().getName();
		} else if (actionStatement instanceof FieldRemoval) {
			return ((FieldRemoval) actionStatement).getName();
		} else {
			throw new IllegalArgumentException("Invalid delta action type: " + actionStatement.getClass().getName());
		}
	}

	@Override
	public DeltaSubAction getActionStatement() {

		return actionStatement;
	}

	@Override
	public DeltaModule getDeltaModule() {

		return getClassAction().getDeltaModule();
	}

	@Override
	public Program getProgram() {

		return getClassAction().getProgram();
	}

	@Override
	public DeltaJActionType getActionType() {

		return actionType;
	}

	@Override
	public DeltaJActionTargetType getTargetType() {

		return targetType;
	}

	@Override
	public String getTargetName() {

		return getClassAction().getTargetName() + "." + targetName;
	}

	@Override
	public Map<String, DeltaJModuleReference> findModuleReferences() {

		return getClassAction().findModuleReferences();
	}

	@Override
	public IDeltaJClassAction getParentAction() {

		return getClassAction();
	}

	private IDeltaJClassAction getClassAction() {

		ClassModification modifiesClass = (ClassModification) actionStatement.eContainer();
		return DeltaJActionFactory.get(modifiesClass);
	}
}
