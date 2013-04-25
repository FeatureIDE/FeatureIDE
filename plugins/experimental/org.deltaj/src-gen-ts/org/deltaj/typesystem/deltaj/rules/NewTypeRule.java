package org.deltaj.typesystem.deltaj.rules;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;
import it.xtypes.runtime.Variable;

public class NewTypeRule extends DeltaJTypeSystemRule {

	protected Variable<org.deltaj.deltaj.ClassType> var_classType = new Variable<org.deltaj.deltaj.ClassType>(
			createEClassifierType(basicPackage.getClassType()));

	protected Variable<org.deltaj.deltaj.New> var_n = new Variable<org.deltaj.deltaj.New>(
			createEClassifierType(basicPackage.getNew()));

	protected Variable<org.deltaj.deltaj.Type> var_t = new Variable<org.deltaj.deltaj.Type>(
			createEClassifierType(basicPackage.getType()));

	protected TypingJudgmentEnvironment env_G = new TypingJudgmentEnvironment();

	public NewTypeRule() {
		this("New", "|-", ":");
	}

	public NewTypeRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	@Override
	public Variable<org.deltaj.deltaj.New> getLeft() {
		return var_n;
	}

	@Override
	public Variable<org.deltaj.deltaj.Type> getRight() {
		return var_t;
	}

	@Override
	public TypingJudgmentEnvironment getEnvironment() {
		return env_G;
	}

	@Override
	public void setEnvironment(TypingJudgmentEnvironment environment) {
		if (environment != null)
			env_G = environment;
	}

	@Override
	public RuntimeRule newInstance() {
		return new NewTypeRule("New", "|-", ":");
	}

	@Override
	public void applyImpl() throws RuleFailedException {

		var_classType = new Variable<org.deltaj.deltaj.ClassType>(
				createEClassifierType(basicPackage.getClassType()),
				factory.createClassType());

		// check var_classType
		if (var_classType.getValue() == null) {
			var_classType.setValue(factory.createClassType());
		}

		var_classType.getValue().setClassref(var_n.getValue().getClass_());

		assignment(var_t, var_classType);

		// final check for variable initialization

		/* check var_t */
		if (var_t.getValue() == null) {
			var_t.setValue(factory.createType());
		}

	}

}
