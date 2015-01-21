package org.deltaj.typesystem.deltaj.rules;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;
import it.xtypes.runtime.Variable;

public class AndOrExpressionTypeRule extends DeltaJTypeSystemRule {

	protected Variable<org.deltaj.deltaj.BooleanType> var_leftType = new Variable<org.deltaj.deltaj.BooleanType>(
			createEClassifierType(basicPackage.getBooleanType()));

	protected Variable<org.deltaj.deltaj.BooleanType> var_rightType = new Variable<org.deltaj.deltaj.BooleanType>(
			createEClassifierType(basicPackage.getBooleanType()));

	protected Variable<org.deltaj.deltaj.AndOrExpression> var_exp = new Variable<org.deltaj.deltaj.AndOrExpression>(
			createEClassifierType(basicPackage.getAndOrExpression()));

	protected Variable<org.deltaj.deltaj.Type> var_t = new Variable<org.deltaj.deltaj.Type>(
			createEClassifierType(basicPackage.getType()));

	protected TypingJudgmentEnvironment env_G = new TypingJudgmentEnvironment();

	public AndOrExpressionTypeRule() {
		this("AndOrExpression", "|-", ":");
	}

	public AndOrExpressionTypeRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	@Override
	public Variable<org.deltaj.deltaj.AndOrExpression> getLeft() {
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
		return new AndOrExpressionTypeRule("AndOrExpression", "|-", ":");
	}

	@Override
	public void applyImpl() throws RuleFailedException {

		var_leftType = new Variable<org.deltaj.deltaj.BooleanType>(
				createEClassifierType(basicPackage.getBooleanType()),
				factory.createBooleanType());

		var_rightType = new Variable<org.deltaj.deltaj.BooleanType>(
				createEClassifierType(basicPackage.getBooleanType()),
				factory.createBooleanType());

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
