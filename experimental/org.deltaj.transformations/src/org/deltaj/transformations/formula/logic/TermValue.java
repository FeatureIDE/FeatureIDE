package org.deltaj.transformations.formula.logic;

public enum TermValue {

	// note that the order is important!
	FALSE('0'),
	TRUE('1'),
	DONTCARE('_');

	private char theChar;

	private TermValue(char theChar) {

		this.theChar = theChar;
	}

	public char getChar() {

		return theChar;
	}

	@Override
	public String toString() {

		return "" + getChar();
	}
}
