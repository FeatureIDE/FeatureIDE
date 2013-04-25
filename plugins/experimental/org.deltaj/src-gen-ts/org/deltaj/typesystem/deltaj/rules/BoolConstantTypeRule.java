package org.deltaj.typesystem.deltaj.rules;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;
import it.xtypes.runtime.Variable;

public class BoolConstantTypeRule extends DeltaJTypeSystemRule {

	protected Variable<org.deltaj.deltaj.BooleanType> var_b = new Variable<org.deltaj.deltaj.BooleanType>(
			createEClassifierType(basicPackage.getBooleanType()));

	protected Variable<org.deltaj.deltaj.BoolConstant> var_c = new Variable<org.deltaj.deltaj.BoolConstant>(
			createEClassifierType(basicPackage.getBoolConstant()));

	protected Variable<org.deltaj.deltaj.Type> var_t = new Variable<org.deltaj.deltaj.Type>(
			createEClassifierType(basicPackage.getType()));

	protected TypingJudgmentEnvironment env_G = new TypingJudgmentEnvironment();

	public BoolConstantTypeRule() {
		this("BoolConstant", "|-", ":");
	}

	public BoolConstantTypeRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	@Override
	public Variable<org.deltaj.deltaj.BoolConstant> getLeft() {
		return var_c;
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
		return new BoolConstantTypeRule("BoolConstant", "|-", ":");
	}

	@Override
	public void applyImpl() throws RuleFailedException {

		var_b = new Variable<org.deltaj.deltaj.BooleanType>(
				createEClassifierType(basicPackage.getBooleanType()),
				factory.createBooleanType());

		// check var_b
		if (var_b.getValue() == null) {
			var_b.setValue(factory.createBooleanType());
		}

		var_b.getValue().setBasic("boolean");

		assignment(var_t, var_b);

		// final check for variable initialization

		/* check var_t */
		if (var_t.getValue() == null) {
			var_t.setValue(factory.createType());
		}

	}

}
