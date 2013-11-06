package br.ufal.ic.colligens.refactoring.tree;

import br.ufal.ic.colligens.refactoring.tree.visitor.Visitor;

public class UnaryExpr extends Node {

	private String kind;
	
	public String getKind() {
		return kind;
	}

	public void setKind(String kind) {
		this.kind = kind;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.run(this);
	}

}
