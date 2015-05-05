/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

public final class Constraints {
	
	/**
	 * Converts a given constraint <c>c</c> to a string, but automatically surrounds
	 * feature names with braces if a feature name is a also an operator.<br/><br/>
	 * <b>Example</b></br>
	 * <code>
	 * Constraint c = new Constraint(fm, new Implies(new Literal("A"), new Literal("implies")));
	 * </code>
	 * The constraint <code>c</code> is printed to <code>A implies "implies"</code>
	 * @param c The constraint
	 * @return A string representation
	 */
	public static final String autoQuote(final Constraint constraint) {
		
		final String c = constraint.getNode().toString(NodeWriter.shortSymbols);
		
		// Quote features that has the same name as an operator, e.g. Feature 
		// implies will be "implies" afterwards
		String printable = quoteOperatorNames(c);
		
		// ATTENTION: Backwards iteration is used here, to first replace "<=>" with "iff".
		// That's because "=>" comes before "<=>" in "shortSymbols", such that "<=>" will
		// be replaces by "<implies"" when not iterating backwards.
		for (int i = NodeWriter.shortSymbols.length - 1; i > 0; i--) {
			printable = printable.replace(NodeWriter.shortSymbols[i].trim(), NodeWriter.textualSymbols[i].trim());
		}
		
		return printable.toString().trim();
	}

	/**
	 * @param c
	 * @return
	 */
	private static String quoteOperatorNames(final String c) {
		final String[] contents = split(c);
		for (int i = 0; i < contents.length; i++) {
			for (final String op : Operator.NAMES) {
				if (contents[i].trim().equals(op.toLowerCase()))
					contents[i] = "\"" + contents[i].trim() + "\" ";
			}
		}
		
		final StringBuilder print = new StringBuilder();
		for (final String content : contents) {
			if (!content.trim().isEmpty()) {	
				print.append(content);
			}
		}
		return print.toString();
	}

	private static String[] split(final String string) {
		final List<String> components = new ArrayList<>();
		final String[] splitted = string.split(" ");
		boolean quotes = false;
		String word = "";
		for (int i = 0; i < splitted.length; i++) {
			if (splitted[i].startsWith("\"") || splitted[i].endsWith("\"")) {
				quotes = !quotes;
			}
			word += splitted[i] + " ";
			
			if (!quotes) {
				components.add(word);
				word = "";
			}
		}		
		return components.toArray(new String[components.size()]);
	}
}
