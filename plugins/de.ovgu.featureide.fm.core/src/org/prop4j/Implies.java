package org.prop4j;

import java.util.List;

/**
 * A constraint that is true iff the left child is false or the right child is
 * true.
 * 
 * @author Thomas Thüm
 */
public class Implies extends Node {
	
	public Implies(Object leftChild, Object rightChild) {
		setChildren(leftChild, rightChild);
	}
	
	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		super.eliminate(list);
		if (list.contains(getClass()))
			return new Or(new Not(children[0]), children[1]);
		return this;
	}
	
	@Override
	public boolean equals(Object object) {
		if (!getClass().isInstance(object))
			return false;
		Implies implies = (Implies) object;
		return children[0].equals(implies.children[0]) && children[1].equals(implies.children[1]);
	}
	
	@Override
	public Node clone() {
		return new Implies(children[0].clone(), children[1].clone());
	}

}
