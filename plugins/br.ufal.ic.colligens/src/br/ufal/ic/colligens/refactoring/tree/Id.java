package br.ufal.ic.colligens.refactoring.tree;

import br.ufal.ic.colligens.refactoring.tree.visitor.Visitor;

public class Id extends Node {

	private String name;

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}
	
	@Override
	public void accept(Visitor visitor) {
        visitor.run(this);    
    }
	
	@Override
	public boolean equals(Object obj) {
		if (this.getClass().getCanonicalName().equals(obj.getClass().getCanonicalName())){
			Node objNod = (Node) obj;
			
			if (objNod instanceof Id){
				if (this instanceof Id){
					if ( !((Id)objNod).getName().equals(this.getName()) ){
						return false;
					}
				}
			}
			
		} else {
			return false;
		}
		return true;
	}
}
