package org.prop4j;

import java.util.List;

/**
 * A constraint that is true iff exactly a specified number of children is
 * true.
 * 
 * @author Thomas Thüm
 */
public class Choose extends Node {
	
	public int n;

	public Choose(int n, Object ...children) {
		this.n = n;
		setChildren(children);
	}

	public Choose(int n, Node[] children) {
		this.n = n;
		setChildren(children);
	}

	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		super.eliminate(list);
		if (!list.contains(getClass()))
			return this;

		return new And(new AtMost(n, clone(children)), new AtLeast(n, clone(children)));
	}

	@Override
	public Node clone() {
		return new Choose(n, clone(children));
	}

}
