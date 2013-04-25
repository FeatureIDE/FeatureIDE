package org.deltaj.typesystem.deltaj.rules;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;
import it.xtypes.runtime.Variable;

public class ThisTypeRule extends DeltaJTypeSystemRule {

	protected Variable<org.deltaj.deltaj.This> var_t = new Variable<org.deltaj.deltaj.This>(
			createEClassifierType(basicPackage.getThis()));

	protected Variable<org.deltaj.deltaj.Type> right_var;

	protected TypingJudgmentEnvironment env_G = new TypingJudgmentEnvironment();

	public ThisTypeRule() {
		this("This", "|-", ":");
	}

	public ThisTypeRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	@Override
	public Variable<org.deltaj.deltaj.This> getLeft() {
		return var_t;
	}

	@Override
	public Variable<org.deltaj.deltaj.Type> getRight() {
		if (right_var == null)
			right_var = new Variable<org.deltaj.deltaj.Type>(
					createEClassifierType(basicPackage.getType()), null);
		return right_var;
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
		return new ThisTypeRule("This", "|-", ":");
	}

	@Override
	public void applyImpl() throws RuleFailedException {
		// axiom

		getRight().setValue(
				castto(env(env_G, "this"), org.deltaj.deltaj.Type.class));

	}

}
