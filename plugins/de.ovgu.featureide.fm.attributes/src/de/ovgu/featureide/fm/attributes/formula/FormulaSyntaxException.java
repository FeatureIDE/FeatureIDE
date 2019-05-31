package de.ovgu.featureide.fm.attributes.formula;

public class FormulaSyntaxException extends Exception {
	
	private int pos;
	private int symbol;
	public FormulaSyntaxException(int pos, int symbol) {
		super(buildErrorMessage(pos, symbol));
		this.pos = pos;
		this.symbol = symbol;
	}
	
	private static String buildErrorMessage(int pos, int symbol) {
		return "Unexpected symbol at " + String.valueOf(pos) + ": " + (char) symbol; 
	}

	public int getPos() {
		return pos;
	}

	public int getSymbol() {
		return symbol;
	}

}
