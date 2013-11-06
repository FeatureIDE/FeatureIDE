package br.ufal.ic.colligens.refactoring.tree;

import br.ufal.ic.colligens.refactoring.tree.visitor.Visitor;
import de.fosd.typechef.featureexpr.FeatureExpr;

public class Opt extends Node {

	private FeatureExpr conditional;
	
	public FeatureExpr getConditional() {
		return conditional;
	}

	public void setConditional(FeatureExpr conditional) {
		this.conditional = conditional;
	}
	
	@Override
	public void accept(Visitor visitor) {
		visitor.run(this);
	}

}
