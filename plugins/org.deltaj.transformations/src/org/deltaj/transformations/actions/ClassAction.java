package org.deltaj.transformations.actions;

import java.util.Map;
import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.transformations.exceptions.DeltaJInvalidActionType;
import org.deltaj.transformations.finder.DeltaJModuleReferenceFinder;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

class ClassAction implements IDeltaJClassAction {

	private final DeltaAction actionStatement;
	private final DeltaJActionType actionType;
	private final DeltaJActionTargetType targetType;

	protected ClassAction(DeltaAction actionStatement) {

		this.actionStatement = actionStatement;
		this.actionType = determineType();
		this.targetType = determineTargetType();
	}

	private DeltaJActionType determineType() {

		if (actionStatement instanceof ClassAddition) {
			return DeltaJActionType.ADDITION;
		} else if (actionStatement instanceof ClassModification) {
			return DeltaJActionType.MODIFICATION;
		} else if (actionStatement instanceof ClassRemoval) {
			return DeltaJActionType.REMOVAL;
		} else {
			throw new DeltaJInvalidActionType(actionStatement);
		}
	}

	private DeltaJActionTargetType determineTargetType() {

		if (actionStatement instanceof ClassAddition || actionStatement instanceof ClassModification
				|| actionStatement instanceof ClassRemoval) {
			return DeltaJActionTargetType.CLASS;
		} else {
			throw new DeltaJInvalidActionType(actionStatement);
		}
	}

	@Override
	public DeltaAction getActionStatement() {

		return this.actionStatement;
	}

	@Override
	public DeltaModule getDeltaModule() {

		return (DeltaModule) this.actionStatement.eContainer();
	}

	@Override
	public Program getProgram() {

		return (Program) this.getDeltaModule().eContainer();
	}

	@Override
	public String getTargetName() {

		return determineClassName();
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
	public Map<String, DeltaJModuleReference> findModuleReferences() {

		return new DeltaJModuleReferenceFinder(getDeltaModule()).findMap();
	}

	private String determineClassName() {

		if (actionStatement instanceof ClassAddition) {
			ClassAddition addClass = (ClassAddition) actionStatement;
			return addClass.getClass_().getName();
		} else if (actionStatement instanceof ClassModification) {
			ClassModification modifiesClass = (ClassModification) actionStatement;
			return modifiesClass.getName();
		} else if (actionStatement instanceof ClassRemoval) {
			ClassRemoval removesClass = (ClassRemoval) actionStatement;
			return removesClass.getName();
		} else {
			throw new IllegalArgumentException("Invalid delta action type: " + actionStatement.getClass().getName());
		}
	}

	@Override
	public IDeltaJClassAction getParentAction() {

		return null;
	}
}
