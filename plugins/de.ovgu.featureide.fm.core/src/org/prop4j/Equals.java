package org.prop4j;

import java.util.List;

/**
 * A constraint that is true iff both children have the same boolean value.
 * 
 * @author Thomas Thüm
 */
public class Equals extends Node {
	
	public Equals(Object leftChild, Object rightChild) {
		setChildren(leftChild, rightChild);
	}
	
	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		super.eliminate(list);
		if (list.contains(getClass()))
			return new And(new Or(new Not(children[0].clone()), children[1]),
					new Or(new Not(children[1].clone()), children[0]));
		return this;
	}
	
	@Override
	public Node clone() {
		return new Equals(children[0].clone(), children[1].clone());
	}
	
}
