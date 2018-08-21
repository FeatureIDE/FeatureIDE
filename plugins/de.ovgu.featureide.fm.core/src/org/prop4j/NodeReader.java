/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package org.prop4j;

import static de.ovgu.featureide.fm.core.localization.StringTable.IFF;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPLIES;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_NUMBER_OF_QUOTATION_MARKS;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_POSITIONING_OF_PARENTHESES;

import java.text.ParseException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.prop4j.ErrorType.ErrorEnum;

/**
 * This class can be used to parse propositional formulas.
 *
 * @author Dariusz Krolikowski
 * @author David Broneske
 * @author Fabian Benduhn
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class NodeReader {

	public final static String[] textualSymbols = new String[] { IFF, IMPLIES, "or", "and", "not" };
	public final static String[] shortSymbols = new String[] { "<=>", "=>", "|", "&", "-" };
	public final static String[] logicalSymbols = new String[] { "\u21D4", "\u21D2", "\u2228", "\u2227", "\u00AC" };
	public final static String[] javaSymbols = new String[] { "==", "=>", "||", "&&", "!" };

	private static final String featureNameMarker = "#";
	private static final String subExpressionMarker = "$";
	private static final String replacedFeatureNameMarker = featureNameMarker + "_";
	private static final String replacedSubExpressionMarker = subExpressionMarker + "_";

	private static final Pattern subExpressionPattern = Pattern.compile(Pattern.quote(subExpressionMarker) + "\\d+");
	private static final Pattern featureNamePattern = Pattern.compile(Pattern.quote(featureNameMarker) + "\\d+");

	private static final Pattern parenthesisPattern = Pattern.compile("\\(([^()]*)\\)");
	private static final Pattern quotePattern = Pattern.compile("\\\"(.*?)\\\"");

	private Collection<String> featureNames;

	private String[] symbols = textualSymbols;
	private boolean noValidFeatureName;
	public ErrorType errorType = new ErrorType(ErrorEnum.None);
	private ParseException errorMessage = null;

	private boolean ignoreMissingFeatures = false;
	private boolean ignoreUnparsableSubExpressions = false;

	public void activateShortSymbols() {
		symbols = shortSymbols;
	}

	public void activateTextualSymbols() {
		symbols = textualSymbols;
	}

	public void activateLogicalSymbols() {
		symbols = logicalSymbols;
	}

	public void activateJavaSymbols() {
		symbols = javaSymbols;
	}

	public Node stringToNode(String constraint) {
		return stringToNode(constraint, null);
	}

	public Node stringToNode(String constraint, Collection<String> featureNames) {
		this.featureNames = featureNames;
		errorMessage = null;

		try {
			return parseNode(constraint);
		} catch (final ParseException e) {

			errorMessage = e;
			return null;
		}
	}

	/**
	 * returns true if constraint is well formed
	 *
	 * @param constraint
	 * @return
	 */
	public boolean isWellFormed(String constraint) {
		return stringToNode(constraint, null) != null;
	}

	/**
	 * returns true if constraint is well formed
	 *
	 * @param constraint constraint supposed to be checked
	 * @param featureNames list of feature names
	 * @return true if constraint is well formed
	 */
	public boolean isWellFormed(String constraint, final Collection<String> featureNames) {
		return stringToNode(constraint, featureNames) != null;
	}

	/**
	 * if stringToNode or isWellFormed were called with not well-formed constraint this method returns the error message otherwise empty String
	 *
	 * @return
	 */
	public ParseException getErrorMessage() {
		return errorMessage;
	}

	public boolean getnoValidFeatureName() {
		return noValidFeatureName;
	}

	public boolean ignoresMissingFeatures() {
		return ignoreMissingFeatures;
	}

	public void setIgnoreMissingFeatures(boolean ignoreMissingFeatures) {
		this.ignoreMissingFeatures = ignoreMissingFeatures;
	}

	public boolean isIgnoreUnparsableSubExpressions() {
		return ignoreUnparsableSubExpressions;
	}

	public void setIgnoreUnparsableSubExpressions(boolean ignoreUnparsableSubExpressions) {
		this.ignoreUnparsableSubExpressions = ignoreUnparsableSubExpressions;
	}

	/**
	 * Checking expression on correct syntax
	 *
	 * @param constraint constraint (without parenthesis) to convert
	 * @param symbols array containing strings for: iff, implies, or, and, not
	 * @param quotedFeatureNames list of substituted feature names
	 * @param subExpressions list of substituted parenthesis expressions
	 * @return
	 */
	private Node checkExpression(String constraint, List<String> quotedFeatureNames, List<String> subExpressions) throws ParseException {
		constraint = " " + constraint + " ";
		if ("  ".equals(constraint)) {
			errorType.setError(ErrorEnum.Default);
			return handleInvalidExpression("Sub expression is empty", "");
		}
		// traverse all symbols
		for (int i = 0; i < symbols.length; i++) {
			final Matcher matcher = Pattern.compile("\\s+(" + Pattern.quote(symbols[i]) + ")\\s+").matcher(constraint);
			while (matcher.find()) {
				// 1st symbol occurrence
				final int index = matcher.start(1);

				// recursion for children nodes
				final String leftSide = constraint.substring(0, index).trim();
				final String rightSide = constraint.substring(index + symbols[i].length(), constraint.length()).trim();

				final Node node1, node2;
				if (i == 4) {
					node1 = null;

					if (rightSide.isEmpty()) {
						errorType.setError(ErrorEnum.Default);
						node2 = handleInvalidExpression("Missing feature name or expression", constraint);

					} else {
						node2 = checkExpression(rightSide, quotedFeatureNames, subExpressions);
					}

				} else {
					if (leftSide.isEmpty()) {
						errorType = new ErrorType(ErrorEnum.InvalidExpressionLeft, matcher.start(), matcher.end());

						node1 = handleInvalidExpression("Missing feature name or expression on left side", constraint);
					} else {
						node1 = checkExpression(leftSide, quotedFeatureNames, subExpressions);
					}
					if (rightSide.isEmpty()) {
						errorType = new ErrorType(ErrorEnum.InvalidExpressionRight, matcher.start(), matcher.end());
						node2 = handleInvalidExpression("Missing feature name or expression on right side", constraint);
					} else {
						node2 = checkExpression(rightSide, quotedFeatureNames, subExpressions);
					}

				}

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
		constraint = constraint.trim();
		final Matcher subExpressionMatcher = subExpressionPattern.matcher(constraint);
		if (subExpressionMatcher.find()) {
			if ((subExpressionMatcher.start() == 0) && (subExpressionMatcher.end() == constraint.length())) {
				return checkExpression(subExpressions.get(Integer.parseInt(constraint.substring(1))).trim(), quotedFeatureNames, subExpressions);
			} else {
				errorType.setError(ErrorEnum.Default);
				return handleInvalidExpression("Missing operator", constraint);
			}
		} else {
			String featureName;
			final Matcher featureNameMatcher = featureNamePattern.matcher(constraint);
			if (featureNameMatcher.find()) {
				if ((featureNameMatcher.start() == 0) && (featureNameMatcher.end() == constraint.length())) {
					featureName = quotedFeatureNames.get(Integer.parseInt(constraint.substring(1)));
				} else {
					errorType.setError(ErrorEnum.Default);
					return handleInvalidExpression("Missing operator", constraint);
				}
			} else {
				if (constraint.contains(" ")) {
					errorType = new ErrorType(ErrorEnum.InvalidFeatureName, constraint);
					return handleInvalidFeatureName(constraint);
				}
				featureName = constraint;
			}
			featureName = featureName.replace(replacedFeatureNameMarker, featureNameMarker).replace(replacedSubExpressionMarker, subExpressionMarker);
			if ((featureNames != null) && !featureNames.contains(featureName)) {

				errorType = new ErrorType(ErrorEnum.InvalidFeatureName, featureName);
				return handleInvalidFeatureName(featureName);
			}
			return new Literal(featureName);
		}
	}

	private Node handleInvalidFeatureName(String featureName) throws ParseException {

		return getInvalidLiteral("'" + featureName + "' is no valid feature name", featureName, ignoreMissingFeatures);
	}

	private Node handleInvalidExpression(String message, String constraint) throws ParseException {
		return getInvalidLiteral(message, constraint, ignoreUnparsableSubExpressions);
	}

	private Node getInvalidLiteral(String message, String element, boolean ignoreError) throws ParseException {
		if (ignoreError) {
			return new ErrorLiteral(element);
		} else {
			throw new ParseException(message, 0);
		}
	}

	private Node parseNode(String constraint) throws ParseException {
		constraint = constraint.trim();
		if (constraint.isEmpty()) {
			throw new ParseException("Contraint is empty", 0);
		}

		int parenthesisCounter = 0;
		boolean quoteSign = false;
		for (int i = 0; i < constraint.length(); i++) {
			final char curChar = constraint.charAt(i);
			switch (curChar) {
			case '(':
				if (quoteSign) {
					errorType.setError(ErrorEnum.Default);
					throw new ParseException(INVALID_POSITIONING_OF_PARENTHESES + ": parenthesis are not allowed in feature names", i);
				}
				parenthesisCounter++;
				break;
			case '\"':
				quoteSign = !quoteSign;
				break;
			case ')':
				if (quoteSign) {
					errorType.setError(ErrorEnum.Default);
					throw new ParseException(INVALID_POSITIONING_OF_PARENTHESES + ": parenthesis are not allowed in feature names", i);
				}
				if (--parenthesisCounter < 0) {
					errorType.setError(ErrorEnum.Default);
					throw new ParseException(INVALID_POSITIONING_OF_PARENTHESES + ": to many closing parentheses", i);
				}
				break;
			default:
				break;
			}
		}
		if (quoteSign) {
			throw new ParseException(INVALID_NUMBER_OF_QUOTATION_MARKS, 0);
		}
		if (parenthesisCounter > 0) {
			errorType.setError(ErrorEnum.Default);
			throw new ParseException(INVALID_POSITIONING_OF_PARENTHESES + ": there are unclosed opening parentheses", 0);
		}

		constraint = constraint.replace(featureNameMarker, replacedFeatureNameMarker);
		constraint = constraint.replace(subExpressionMarker, replacedSubExpressionMarker);

		final ArrayList<String> quotedFeatureNames = new ArrayList<>();
		final ArrayList<String> subExpressions = new ArrayList<>();
		if (constraint.contains("\"")) {
			constraint = replaceGroup(constraint, featureNameMarker, quotedFeatureNames, quotePattern);
		}
		while (constraint.contains("(")) {
			constraint = replaceGroup(constraint, subExpressionMarker, subExpressions, parenthesisPattern);
		}

		return checkExpression(constraint, quotedFeatureNames, subExpressions);
	}

	private String replaceGroup(String constraint, String marker, final List<String> groupList, final Pattern pattern) {
		int counter = groupList.size();

		final ArrayList<Integer> positionList = new ArrayList<>();
		final Matcher matcher = pattern.matcher(constraint);
		positionList.add(0);
		while (matcher.find()) {
			groupList.add(matcher.group(1));
			positionList.add(matcher.start());
			positionList.add(matcher.end());
		}
		positionList.add(constraint.length());

		final StringBuilder sb = new StringBuilder(constraint.substring(positionList.get(0), positionList.get(1)));
		for (int i = 2; i < positionList.size(); i += 2) {
			sb.append(marker);
			sb.append(counter++);
			sb.append(constraint.substring(positionList.get(i), positionList.get(i + 1)));
		}
		return sb.toString();
	}

}
