package org.deltaj.typesystem.deltaj.rules;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;
import it.xtypes.runtime.Variable;

public class PlusTypeRule extends DeltaJTypeSystemRule {

	protected Variable<org.deltaj.deltaj.BasicType> var_leftType = new Variable<org.deltaj.deltaj.BasicType>(
			createEClassifierType(basicPackage.getBasicType()));

	protected Variable<org.deltaj.deltaj.BasicType> var_rightType = new Variable<org.deltaj.deltaj.BasicType>(
			createEClassifierType(basicPackage.getBasicType()));

	protected Variable<org.deltaj.deltaj.Plus> var_plus = new Variable<org.deltaj.deltaj.Plus>(
			createEClassifierType(basicPackage.getPlus()));

	protected Variable<org.deltaj.deltaj.Type> var_t = new Variable<org.deltaj.deltaj.Type>(
			createEClassifierType(basicPackage.getType()));

	protected TypingJudgmentEnvironment env_G = new TypingJudgmentEnvironment();

	public PlusTypeRule() {
		this("Plus", "|-", ":");
	}

	public PlusTypeRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	@Override
	public Variable<org.deltaj.deltaj.Plus> getLeft() {
		return var_plus;
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
		return new PlusTypeRule("Plus", "|-", ":");
	}

	@Override
	public void applyImpl() throws RuleFailedException {

		var_leftType = new Variable<org.deltaj.deltaj.BasicType>(
				createEClassifierType(basicPackage.getBasicType()),
				factory.createBasicType());

		var_rightType = new Variable<org.deltaj.deltaj.BasicType>(
				createEClassifierType(basicPackage.getBasicType()),
				factory.createBasicType());

		applyTypeRule(env_G, var_plus.getValue().getLeft(), var_leftType);

		applyTypeRule(env_G, var_plus.getValue().getRight(), var_rightType);

		boolean or_temp_1 = false;
		// first or branch
		try {

			equals(var_leftType.getValue().getBasic(), "String");

			assignment(var_t, var_leftType);

			or_temp_1 = true;
		} catch (Throwable e) {
			registerFailure(e);
			// go on with other branches
		}

		try {
			if (!or_temp_1) {

				equals(var_rightType.getValue().getBasic(), "String");

				assignment(var_t, var_rightType);

				or_temp_1 = true;
			}
		} catch (Throwable e) {
			registerFailure(e);
			// go on with other branches
		}

		// last or branch
		if (!or_temp_1) {
			try {
				equals(var_leftType.getValue().getBasic(), "int");

				equals(var_rightType.getValue().getBasic(), "int");

				assignment(var_t, var_leftType);

			} catch (Throwable e) {
				registerAndThrowFailure(e);
			}
		}

		// final check for variable initialization

		/* check var_t */
		if (var_t.getValue() == null) {
			var_t.setValue(factory.createType());
		}

	}

}
