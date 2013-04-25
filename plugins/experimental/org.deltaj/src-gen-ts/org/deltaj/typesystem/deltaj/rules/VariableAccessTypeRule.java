package org.deltaj.typesystem.deltaj.rules;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;
import it.xtypes.runtime.Variable;

public class VariableAccessTypeRule extends DeltaJTypeSystemRule {

	protected Variable<org.deltaj.deltaj.VariableAccess> var_v = new Variable<org.deltaj.deltaj.VariableAccess>(
			createEClassifierType(basicPackage.getVariableAccess()));

	protected Variable<org.deltaj.deltaj.Type> var_t = new Variable<org.deltaj.deltaj.Type>(
			createEClassifierType(basicPackage.getType()));

	protected TypingJudgmentEnvironment env_G = new TypingJudgmentEnvironment();

	public VariableAccessTypeRule() {
		this("VariableAccess", "|-", ":");
	}

	public VariableAccessTypeRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	@Override
	public Variable<org.deltaj.deltaj.VariableAccess> getLeft() {
		return var_v;
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
		return new VariableAccessTypeRule("VariableAccess", "|-", ":");
	}

	@Override
	public void applyImpl() throws RuleFailedException {

		assignment(var_t, var_v.getValue().getVariable().getType());

		// final check for variable initialization

		/* check var_t */
		if (var_t.getValue() == null) {
			var_t.setValue(factory.createType());
		}

	}

}
