package org.prop4j;

import java.util.List;

/**
 * A constraint that is true iff at least a specified number of children is
 * true.
 * 
 * @author Thomas Thüm
 */
public class AtLeast extends Node {
	
	public int min;

	public AtLeast(int min, Object ...children) {
		this.min = min;
		setChildren(children);
	}

	public AtLeast(int min, Node[] children) {
		this.min = min;
		setChildren(children);
	}

	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		super.eliminate(list);
		if (!list.contains(getClass()))
			return this;
		
		Node[] newNodes = chooseKofN(children, children.length - min + 1, false);
		return new And(newNodes);
	}

	@Override
	public Node clone() {
		return new AtLeast(min, clone(children));
	}

}
