package de.ovgu.featureide.fm.extended.ui.io.constraint;

public enum RelationOperator {
	EQUAL("="),
	GREATER_EQUAL(">="),
	LESSER_EQUAL("<=");
	
	private String symbol;
	
	private RelationOperator(String symbol) {
		this.symbol = symbol;
	}
	
	@Override
	public String toString() {
		return symbol;
	}
	
	public static RelationOperator parseOperator(String string) {
		RelationOperator op = null;
		
		if (string.equals(EQUAL.toString())) {
			op = EQUAL;
		} else if (string.equals(GREATER_EQUAL.toString())) {
			op = GREATER_EQUAL;
		} else if (string.equals(LESSER_EQUAL.toString())) {
			op = LESSER_EQUAL;
		}
		
		return op;
	}
}
