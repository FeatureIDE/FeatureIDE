package org.deltaj.transformations.formula.logic;

class TermParser {

	private final static String PATTERN = "[01" + TermValue.DONTCARE.getChar() + "]*";
	private final String termText;

	public TermParser(byte variableCount, String termText) {

		this.termText = termText;

		if (!termText.matches(PATTERN)) {
			throw new IllegalArgumentException(String.format("The term '%s' does not match the pattern '%s'.", termText, PATTERN));
		}

		if (termText.length() != variableCount) {
			throw new IllegalArgumentException(String.format("The term '%s' must contain exactly %d variables.", termText, variableCount));
		}
	}

	public int parse() {

		int variables = 0;

		for (int i = 0; i < termText.length(); ++i) {

			char c = termText.charAt(i);

			if (c == '1') {
				variables |= 1 << 2 * i;
			}

			if (c == TermValue.DONTCARE.getChar()) {
				variables |= 2 << 2 * i;
			}
		}

		return variables;
	}
}
