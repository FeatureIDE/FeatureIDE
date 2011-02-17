package org.prop4j;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * 
 * @author Dariusz Krolikowski
 * @author Dave Broneske
 * @author Fabian Benduhn
 * 
 */

public class NodeReader {

	public final static String[] textualSymbols = new String[] { " iff ",
			" implies ", " or ", " and ", "not " };

	public final static String[] shortSymbols = new String[] { " <=> ", " => ",
			" | ", " & ", "- " };

	public final static String[] logicalSymbols = new String[] { " \u21D4 ",
			" \u21D2 ", " \u2228 ", " \u2227 ", "\u00AC " };

	private static final String[] OPERATOR_NAMES = { " Not ", " And ", " Or ",
			" Implies ", " Iff ", "(", ")" /* "At most 1" */};

	private List<String> featureNames;
	private String errorMessage;
	private boolean isWellFormed;
	private boolean hasFeatureNames;
	private String iff, implies, or, and, not;

	/**
	 * Converts the given constraint (textual representation) into a node
	 * 
	 * @param string
	 *            constraint to convert
	 * @return node
	 */

	/**
	 * Converts the given constraint into a node
	 * 
	 * @param string
	 *            constraint to convert
	 * @param symbols
	 *            array containing strings for: iff, implies, or, and, not
	 * @return node
	 */

	public NodeReader() {
		activateTextualSymbols();
		errorMessage = "";
		hasFeatureNames = false;
	}

	public Node stringToNode(String constraint) {

		isWellFormed = wellformed(constraint);
		if (!isWellFormed) {

			return null;

		}
		return getNode(constraint);
	}

	public Node stringToNode(String constraint, List<String> featureNames) {
		this.featureNames = featureNames;

		errorMessage = "";

		if (featureNames == null) {
			hasFeatureNames = false;
		} else {
			hasFeatureNames = true;
		}
		isWellFormed = wellformed(constraint);
		if (!isWellFormed) {

			return null;
		}
		return getNode(constraint);
	}

	/**
	 * if stringToNode or isWellFormed were called with not well-formed
	 * constraint this method returns the error message otherwise empty String
	 * 
	 * @return
	 */
	public String getErrorMessage() {
		return errorMessage;
	}

	/**
	 * returns true if constraint is well formed
	 * 
	 * @param constraint
	 * @return
	 */
	public boolean isWellFormed(String constraint) {
		hasFeatureNames = false;
		return wellformed(constraint);
	}

	/**
	 * returns true if constraint is well formed
	 * 
	 * @param constraint
	 * @param featureNames
	 * @return
	 */
	public boolean isWellFormed(String constraint, List<String> featureNames) {
		hasFeatureNames = true;
		this.featureNames = featureNames;
		return wellformed(constraint);
	}

	private Node getNode(String string) {

		string = string.trim();

		while (string.contains("  "))
			string = string.replaceAll("  ", " ");

		// list -> variable for substituting bracket expressions
		LinkedList<String> list = new LinkedList<String>();
		int counter = 0;

		// finding all bracket expressions
		while (string.contains(")")) {
			int indEnd = string.indexOf(")");
			int indStart = string.substring(0, indEnd).lastIndexOf("(");

			// inner bracket found -> substitution to list
			list.add(string.substring(indStart + 1, indEnd));
			string = string.substring(0, indStart) + counter
					+ string.substring(indEnd + 1, string.length());
			counter++;
		}
		return stringToNodeRec(string, textualSymbols, list);
	}

	/**
	 * Creating nodes out of constraints
	 * 
	 * @param string
	 *            constraint (without brackets) to convert
	 * @param symbols
	 *            array containing strings for: iff, implies, or, and, not
	 * @param list
	 *            list of substituted bracket expressions
	 * @return
	 */
	private static Node stringToNodeRec(String string, String[] symbols,
			LinkedList<String> list) {

		string = string.trim();

		// traverse all symbols
		for (int i = 0; i < symbols.length; i++) {
			while (string.contains(symbols[i])) {
				int index = string.indexOf(symbols[i]); // 1st symbol occurrence

				// recursion for children nodes
				Node node1 = stringToNodeRec(string.substring(0, index),
						symbols, list);
				Node node2 = stringToNodeRec(
						string.substring(index + symbols[i].length(),
								string.length()), symbols, list);

				switch (i) {
				case 0: {
					return new Equals(node1, node2);
				}
				case 1: {
					return new Implies(node1, node2);
				}
				case 2: {
					return new Or(node1, node2);
				}
				case 3: {
					return new And(node1, node2);
				}
				case 4: {
					return new Not(node2); // Not - only one argument

				}
				}
			}
		}

		if (isIntNumber(string)) {
			return stringToNodeRec(list.get(Integer.parseInt(string)), symbols,
					list);
		} else {
			return new Literal(string);
		}
	}

	/**
	 * Checks, if num is an integer number
	 * 
	 * @param num
	 *            number to check
	 * @return true, if num is an integer number, false otherwise
	 */
	private static boolean isIntNumber(String num) {
		try {
			Integer.parseInt(num);
		} catch (NumberFormatException nfe) {
			return false;
		}
		return true;
	}

	private boolean wellformed(String constraint) {

		constraint = reduceWhiteSpaces(insertWhitespacesAtBrackets(constraint)
				.trim());
		if (!constraint.isEmpty()) {

			ArrayList<String> list = new ArrayList<String>();
			list.add(and);
			list.add(or);
			list.add(iff);
			list.add(implies);
			list.add(")");

			ArrayList<String> operators = new ArrayList<String>();
			for (int i = 0; i < OPERATOR_NAMES.length; i++) {
				operators.add(OPERATOR_NAMES[i].toLowerCase().trim());
			}

			// checking number of brackets
			int bracketCounter = 0;
			for (int i = 0; i < constraint.length(); i++) {
				if (constraint.charAt(i) == '(') {
					bracketCounter++;
				} else if (constraint.charAt(i) == ')' && bracketCounter == 0) {
					errorMessage = "invalid positioning of parentheses";
					return false;
				} else if (constraint.charAt(i) == ')') {
					bracketCounter--;
				} else {

				}
			}
			if (bracketCounter < 0) {
				errorMessage = "invalid number of parentheses: to many ')'";

				return false;
			} else if (bracketCounter > 0) {
				errorMessage = "invalid number of parentheses: to many '('";

				return false;
			}

			String[] splittedString = constraint.split(" ");

			for (int i = 0; i < splittedString.length; i++) {
				splittedString[i] = splittedString[i].trim();
				if (hasFeatureNames
						&& !(featureNames.contains(splittedString[i]) || operators
								.contains(splittedString[i]))) {
					// one token is no feature name or operator
					errorMessage = "invalid expression: " + splittedString[i];

					return false;
				}

				// every token is feature name, operator or bracket
				if (i == splittedString.length - 1) {
					// token i is last element of constraint
					if (hasFeatureNames) {
						if (!(splittedString[i].equals(")") || featureNames
								.contains(splittedString[i]))) {
							// constraint does not end with ) or feature name
							errorMessage = "constraint cannot end with: "
									+ splittedString[i];

							return false;
						} else {
							// constraint ends with ) or feature name
							return true;
						}
					} else {
						// no feature names given
						if ((splittedString[i].equals("(")
								|| splittedString[i].equals(not)
								|| splittedString[i].equals(and)
								|| splittedString[i].equals(or)
								|| splittedString[i].equals(implies) || splittedString[i]
								.equals(iff))) {
							// constraint does not end with ) or feature name
							errorMessage = "constraint cannot end with: "
									+ splittedString[i];

							return false;
						} else {
							// constraint ends with ) or feature name
							return true;
						}
					}
				}
				// token i is not last element
				if ((splittedString[i].equals("(")
						|| splittedString[i].equals(not)
						|| splittedString[i].equals(and)
						|| splittedString[i].equals(or)
						|| splittedString[i].equals(iff) || splittedString[i]
						.equals(implies))) {
					// token is one of: (,not,and,or,iff,implies
					if (list.contains(splittedString[i + 1])) {
						// token(i+1) is one of: and,or,iff,implies,)
						errorMessage = "invalid construct: "
								+ splittedString[i] + " "
								+ splittedString[i + 1];

						return false;
					}
					// token(i+1) is one of: (,not,feature name
				} else {
					// token is a feature name or a )
					if (!list.contains(splittedString[i + 1])) {
						// token(i+1) is one of: (,not,feature name
						errorMessage = "invalid construct: "
								+ splittedString[i] + " "
								+ splittedString[i + 1];
						return false;
					}

				}
			}
		}
		return true;
	}

	/**
	 * reduces
	 * 
	 * @param str
	 * @return
	 */

	private static String insertWhitespacesAtBrackets(String str) {
		str = str.replaceAll("\\)", " ) ");
		str = str.replaceAll("\\(", " ( ");
		return str;

	}

	/**
	 * replaces unnecessary white spaces inside str single white spaces are not
	 * deleted
	 * 
	 * @param str
	 * @return
	 */
	public static String reduceWhiteSpaces(String str) {
		if (str.length() < 2)
			return str;
		StringBuffer strBuf = new StringBuffer();
		strBuf.append(str.charAt(0));
		for (int i = 1; i < str.length(); i++) {
			if (!(Character.isWhitespace(str.charAt(i - 1)) && Character
					.isWhitespace(str.charAt(i)))) {
				strBuf.append(str.charAt(i));
			}
		}
		return strBuf.toString();
	}

	// public final static String[] textualSymbols = new String[] { " iff ",
	// " implies ", " or ", " and ", "not " };

	public void activateShortSymbols() {
		iff = shortSymbols[0].trim();
		implies = shortSymbols[1].trim();
		or = shortSymbols[2].trim();
		and = shortSymbols[3].trim();
		not = shortSymbols[4].trim();
	}

	public void activateTextualSymbols() {
		iff = textualSymbols[0].trim();
		implies = textualSymbols[1].trim();
		or = textualSymbols[2].trim();
		and = textualSymbols[3].trim();
		not = textualSymbols[4].trim();
	}

	public void activateLogicalSymbols() {
		iff = logicalSymbols[0].trim();
		implies = logicalSymbols[1].trim();
		or = logicalSymbols[2].trim();
		and = logicalSymbols[3].trim();
		not = logicalSymbols[4].trim();
	}
}
