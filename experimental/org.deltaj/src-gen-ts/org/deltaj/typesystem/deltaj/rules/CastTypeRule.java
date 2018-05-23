package org.deltaj.typesystem.deltaj.rules;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;
import it.xtypes.runtime.Variable;

public class CastTypeRule extends DeltaJTypeSystemRule {

	protected Variable<org.deltaj.deltaj.ClassType> var_classType = new Variable<org.deltaj.deltaj.ClassType>(
			createEClassifierType(basicPackage.getClassType()));

	protected Variable<org.deltaj.deltaj.Cast> var_cast = new Variable<org.deltaj.deltaj.Cast>(
			createEClassifierType(basicPackage.getCast()));

	protected Variable<org.deltaj.deltaj.Type> var_t = new Variable<org.deltaj.deltaj.Type>(
			createEClassifierType(basicPackage.getType()));

	protected TypingJudgmentEnvironment env_G = new TypingJudgmentEnvironment();

	public CastTypeRule() {
		this("Cast", "|-", ":");
	}

	public CastTypeRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	@Override
	public Variable<org.deltaj.deltaj.Cast> getLeft() {
		return var_cast;
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
		return new CastTypeRule("Cast", "|-", ":");
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

		var_classType.getValue().setClassref(var_cast.getValue().getType());

		assignment(var_t, var_classType);

		// final check for variable initialization

		/* check var_t */
		if (var_t.getValue() == null) {
			var_t.setValue(factory.createType());
		}

	}

}
