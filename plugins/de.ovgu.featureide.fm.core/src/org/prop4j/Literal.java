package org.prop4j;

import java.util.List;

/**
 * A variable or negated variable.
 * 
 * @author Thomas Th�m
 */
public class Literal extends Node {
	
	public Object var;
	
	public boolean positive;

	public Literal(Object var, boolean positive) {
		this.var = var;
		this.positive = positive;
	}
	
	public Literal(Object var) {
		this.var = var;
		positive = true;
	}

	public void flip() {
		positive = !positive;
	}
	
	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		//nothing to do with children
		return this;
	}
	
	@Override
	protected Node clausify() {
		//nothing to do
		return this;
	}
	
	@Override
	public void simplify() { 
		//nothing to do (recursive calls reached lowest node)
	}

	@Override
	public Node clone() {
		return new Literal(var, positive);
	}

	@Override
	public boolean equals(Object node) {
		if (!(node instanceof Literal))
			return false;
		return (var.equals(((Literal) node).var)) && (positive == ((Literal) node).positive);
	}
	
}
