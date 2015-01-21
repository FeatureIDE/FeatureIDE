package org.deltaj.typesystem.deltaj.rules;

import org.deltaj.typesystem.deltaj.DeltaJTypeSystemDefinition;

import it.xtypes.runtime.RuntimeRule;
import it.xtypes.runtime.RuleFailedException;
import it.xtypes.runtime.TypingJudgmentEnvironment;

import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.DeltajPackage;

public abstract class DeltaJTypeSystemRule extends RuntimeRule {

	protected DeltajFactory factory = DeltajFactory.eINSTANCE;

	protected DeltajPackage basicPackage = DeltajPackage.eINSTANCE;

	public DeltaJTypeSystemRule(String ruleName, String typeJudgmentSymbol,
			String typeStatementRelation) {
		super(ruleName, typeJudgmentSymbol, typeStatementRelation);
	}

	public void applyTypeRule(TypingJudgmentEnvironment environment,
			Object left, Object right) throws RuleFailedException {
		addAppliedRuleToTrace(((DeltaJTypeSystemDefinition) runtimeTypeSystem)
				.applyTypeRule(environment, left, right));
	}

}
