package de.ovgu.featureide.fm.core.constraint;

public enum RelationOperator {
	EQUAL("=="),
	NOT_EQUAL("!="),
	GREATER(">"),
	LESS("<"),
	GREATER_EQUAL(">="),
	LESS_EQUAL("<=");
	
	private String symbol;
	
	private RelationOperator(String symbol) {
		this.symbol = symbol;
	}
	
	@Override
	public String toString() {
		return symbol;
	}
}
