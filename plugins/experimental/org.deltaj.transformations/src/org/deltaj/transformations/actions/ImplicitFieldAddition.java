package org.deltaj.transformations.actions;

import java.util.Map;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

class ImplicitFieldAddition implements IDeltaJImplicitFieldAddition {

	private final IDeltaJClassAction classAddition;
	private final Field fieldStatement;

	protected ImplicitFieldAddition(IDeltaJClassAction classAddition, Field fieldStatement) {

		this.classAddition = classAddition;
		this.fieldStatement = fieldStatement;
	}

	@Override
	public Field getActionStatement() {

		return fieldStatement;
	}

	@Override
	public DeltaModule getDeltaModule() {

		return classAddition.getDeltaModule();
	}

	@Override
	public Program getProgram() {

		return classAddition.getProgram();
	}

	@Override
	public DeltaJActionType getActionType() {

		return DeltaJActionType.ADDITION;
	}

	@Override
	public DeltaJActionTargetType getTargetType() {

		return DeltaJActionTargetType.FIELD;
	}

	@Override
	public String getTargetName() {

		return classAddition.getTargetName() + "." + fieldStatement.getName();
	}

	@Override
	public Map<String, DeltaJModuleReference> findModuleReferences() {

		return classAddition.findModuleReferences();
	}

	@Override
	public IDeltaJClassAction getParentAction() {

		return classAddition;
	}
}
