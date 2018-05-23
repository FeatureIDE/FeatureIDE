package org.deltaj.transformations.actions;

import java.util.Map;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

class ImplicitMethodAddition implements IDeltaJImplicitMethodAddition {

	private final IDeltaJClassAction classAddition;
	private final Method methodStatement;

	protected ImplicitMethodAddition(IDeltaJClassAction classAddition, Method methodStatement) {

		this.classAddition = classAddition;
		this.methodStatement = methodStatement;
	}

	@Override
	public Method getActionStatement() {

		return methodStatement;
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

		return DeltaJActionTargetType.METHOD;
	}

	@Override
	public String getTargetName() {

		return classAddition.getTargetName() + "." + methodStatement.getName();
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
