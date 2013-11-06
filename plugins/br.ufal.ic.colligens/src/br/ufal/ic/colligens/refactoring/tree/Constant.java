package br.ufal.ic.colligens.refactoring.tree;

import br.ufal.ic.colligens.refactoring.tree.visitor.Visitor;

public class Constant extends Node{

	private String value;
	
	public String getValue() {
		return value;
	}

	public void setValue(String value) {
		this.value = value;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.run(this);
	}

}
