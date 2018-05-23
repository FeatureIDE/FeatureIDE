package org.deltaj.typesystem.deltaj.rules;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;
import it.xtypes.runtime.Variable;

public class StringConstantTypeRule extends DeltaJTypeSystemRule {

	protected Variable<org.deltaj.deltaj.StringType> var_b = new Variable<org.deltaj.deltaj.StringType>(
			createEClassifierType(basicPackage.getStringType()));

	protected Variable<org.deltaj.deltaj.StringConstant> var_c = new Variable<org.deltaj.deltaj.StringConstant>(
			createEClassifierType(basicPackage.getStringConstant()));

	protected Variable<org.deltaj.deltaj.Type> var_t = new Variable<org.deltaj.deltaj.Type>(
			createEClassifierType(basicPackage.getType()));

	protected TypingJudgmentEnvironment env_G = new TypingJudgmentEnvironment();

	public StringConstantTypeRule() {
		this("StringConstant", "|-", ":");
	}

	public StringConstantTypeRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	@Override
	public Variable<org.deltaj.deltaj.StringConstant> getLeft() {
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
		return new StringConstantTypeRule("StringConstant", "|-", ":");
	}

	@Override
	public void applyImpl() throws RuleFailedException {

		var_b = new Variable<org.deltaj.deltaj.StringType>(
				createEClassifierType(basicPackage.getStringType()),
				factory.createStringType());

		// check var_b
		if (var_b.getValue() == null) {
			var_b.setValue(factory.createStringType());
		}

		var_b.getValue().setBasic("String");

		assignment(var_t, var_b);

		// final check for variable initialization

		/* check var_t */
		if (var_t.getValue() == null) {
			var_t.setValue(factory.createType());
		}

	}

}
