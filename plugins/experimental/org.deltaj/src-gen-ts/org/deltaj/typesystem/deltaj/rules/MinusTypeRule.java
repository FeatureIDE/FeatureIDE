package org.deltaj.typesystem.deltaj.rules;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;
import it.xtypes.runtime.Variable;

public class MinusTypeRule extends DeltaJTypeSystemRule {

	protected Variable<org.deltaj.deltaj.IntType> var_leftType = new Variable<org.deltaj.deltaj.IntType>(
			createEClassifierType(basicPackage.getIntType()));

	protected Variable<org.deltaj.deltaj.IntType> var_rightType = new Variable<org.deltaj.deltaj.IntType>(
			createEClassifierType(basicPackage.getIntType()));

	protected Variable<org.deltaj.deltaj.Minus> var_exp = new Variable<org.deltaj.deltaj.Minus>(
			createEClassifierType(basicPackage.getMinus()));

	protected Variable<org.deltaj.deltaj.Type> var_t = new Variable<org.deltaj.deltaj.Type>(
			createEClassifierType(basicPackage.getType()));

	protected TypingJudgmentEnvironment env_G = new TypingJudgmentEnvironment();

	public MinusTypeRule() {
		this("Minus", "|-", ":");
	}

	public MinusTypeRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	@Override
	public Variable<org.deltaj.deltaj.Minus> getLeft() {
		return var_exp;
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
		return new MinusTypeRule("Minus", "|-", ":");
	}

	@Override
	public void applyImpl() throws RuleFailedException {

		var_leftType = new Variable<org.deltaj.deltaj.IntType>(
				createEClassifierType(basicPackage.getIntType()),
				factory.createIntType());

		var_rightType = new Variable<org.deltaj.deltaj.IntType>(
				createEClassifierType(basicPackage.getIntType()),
				factory.createIntType());

		applyTypeRule(env_G, var_exp.getValue().getLeft(), var_leftType);

		applyTypeRule(env_G, var_exp.getValue().getRight(), var_rightType);

		assignment(var_t, var_leftType);

		// final check for variable initialization

		/* check var_t */
		if (var_t.getValue() == null) {
			var_t.setValue(factory.createType());
		}

	}

}
