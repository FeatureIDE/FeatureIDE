/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core;

import java.util.ArrayList;
import java.util.List;

import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.IConstraint;

/**
 * @author Marcus Pinnecke
 */
public final class Constraints {

	/**
	 * Converts a given constraint <c>c</c> to a string, but automatically surrounds
	 * feature names with braces if a feature name is a also an operator.<br/>
	 * <br/>
	 * <b>Example</b></br> <code>
	 * Constraint c = new Constraint(fm, new Implies(new Literal("A"), new Literal(IMPLIES)));
	 * </code> The constraint <code>c</code> is printed to <code>A implies IMPLIES</code>
	 * 
	 * @param c The constraint
	 * @return A string representation
	 */
	public static final String autoQuote(final IConstraint constraint) {
		final String c = constraint.getNode().toString(NodeWriter.shortSymbols);
		return autoQuote(c);
	}

	public static final String autoQuote(final String constraint) {
		// Quote features that has the same name as an operator, e.g. Feature 
		// implies will be IMPLIES afterwards
		String printable = quoteOperatorNames(constraint);

		// ATTENTION: Backwards iteration is used here, to first replace "<=>WITHiff".
		// That's because "=>COMES_BEFORE<=>INshortSymbolsCOMMA__SUCH_THAT<=>" will
		// be replaces by "<implies"" when not iterating backwards.
		for (int i = NodeWriter.shortSymbols.length - 1; i >= 0; i--)
			printable = printable.replace(NodeWriter.shortSymbols[i].trim(), NodeWriter.textualSymbols[i].trim());
		return printable.toString().trim();
	}

	/**
	 * @param c
	 * @return
	 */
	private static String quoteOperatorNames(final String c) {
		final String[] contents = split(c);
		for (int i = 0; i < contents.length; i++)
			for (final String op : Operator.NAMES)
				if (!(op.equals("(")) && !op.equals(")") && contents[i].trim().equals(op.toLowerCase()))
					contents[i] = "\"" + contents[i].trim() + "\" ";

		final StringBuilder print = new StringBuilder();
		for (final String content : contents)
			if (!content.trim().isEmpty())
				print.append(content);

		return print.toString();
	}

	public static String[] split(final String string) {
		final List<String> components = new ArrayList<>();
		final String[] splitted = splitOnBrackets(mergeByQuotes(splitOnWhiteSpace(string)));

		for (int i = 0; i < splitted.length; i++) {
			components.add(splitted[i] + " ");
		}
		return components.toArray(new String[components.size()]);
	}

	/**
	 * @param splitOnWhiteSpace
	 * @return
	 */
	private static String[] mergeByQuotes(String[] components) {
		List<String> result = new ArrayList<>();
		boolean quoteFlag = false;
		StringBuilder word = new StringBuilder();
		for (int i = 0; i < components.length; i++) {
			if (components[i].contains("\"")) {
				word.append(components[i]);
				if (quoteFlag) {
					result.add(word.toString());
					word = new StringBuilder();
				}

				quoteFlag = !quoteFlag;
				continue;
			}
			if (!quoteFlag)
				result.add(components[i]);
			else {
				word.append(components[i]);
			}
		}

		return result.toArray(new String[result.size()]);
	}

	private static String[] splitOnWhiteSpace(String string) {
		List<String> result = new ArrayList<>();

		StringBuilder word = new StringBuilder();
		for (int i = 0; i < string.length(); i++) {
			if (string.charAt(i) == ' ') {
				
				if (word.length() > 0) {
					result.add(word.toString().trim());
					result.add(" ");
					word = new StringBuilder();
					continue;
				} else {
					result.add(" ");
				}
			} else {
				word.append(string.charAt(i));
			}
		}
		if (word.length() > 0) {
			result.add(word.toString());
		}

		return result.toArray(new String[result.size()]);
	}

	/**
	 * @param split
	 * @return
	 */
	public static String[] splitOnBrackets(String[] split) {
		List<String> result = new ArrayList<>(split.length);
		for (int i = 0; i < split.length; i++) {
			String s = split[i];
			StringBuilder word = new StringBuilder();
			StringBuilder closingBrackets = new StringBuilder();
			for (int k = 0; k < s.length(); k++) {
				if (s.charAt(k) == '(')
					result.add("(");
				else if (s.charAt(k) == ')')
					closingBrackets.append(")");
				else
					word.append(s.charAt(k));
			}
			if (word.length() > 0)
				result.add(word.toString().trim());
			if (closingBrackets.length() > 0)
				result.add(closingBrackets.toString());
		}
		return result.toArray(new String[result.size()]);
	}
}
