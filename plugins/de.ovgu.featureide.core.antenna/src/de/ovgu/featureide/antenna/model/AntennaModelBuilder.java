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
package de.ovgu.featureide.antenna.model;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirectiveCommand;
import de.ovgu.featureide.core.fstmodel.preprocessor.PPModelBuilder;

/**
 * Build the FSTModel for antenna projects.
 *
 * @author Christoph Giesel
 * @author Marcus Kamieth
 * @author Sebastian Krieter
 */
public class AntennaModelBuilder extends PPModelBuilder {

	public static final String OPERATORS = "[\\s!=<>\",;&\\^\\|\\(\\)]";
	public static final String REGEX = "(//\\s*#.*" + OPERATORS + ")(%s)(" + OPERATORS + ")";

	public static final String COMMANDS = "ifdef|if|ifndef|elif|elifdef|elifndef|else|condition|define|undefine|endif";

	Pattern patternCommands = Pattern.compile("//\\s*#(" + COMMANDS + ")");

	public AntennaModelBuilder(IFeatureProject featureProject) {
		super(featureProject);
	}

	/**
	 * returns true if the regular expression regex can be matched by a substring of text
	 */
	protected static boolean containsRegex(String text, String regex) {
		final Pattern pattern = Pattern.compile(regex);
		final Matcher matcher = pattern.matcher(text);
		return matcher.find();
	}

	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		// for preprocessor outline
		final Stack<FSTDirective> directivesStack = new Stack<FSTDirective>();
		final LinkedList<FSTDirective> directivesList = new LinkedList<FSTDirective>();
		int id = 0;

		for (int i = 0; i < lines.size(); i++) {
			String line = lines.get(i);

			// if line is preprocessor directive
			if (containsRegex(line, "//\\s*#")) {
				FSTDirectiveCommand command = null;

				if (containsRegex(line, "//\\s*#if[ (]")) {// 1
					command = FSTDirectiveCommand.IF;
				} else if (containsRegex(line, "//\\s*#ifdef[ (]")) {// 2
					command = FSTDirectiveCommand.IFDEF;
				} else if (containsRegex(line, "//\\s*#ifndef[ (]")) {// 3
					command = FSTDirectiveCommand.IFNDEF;
				} else if (containsRegex(line, "//\\s*#elif[ (]")) {// 4
					command = FSTDirectiveCommand.ELIF;
				} else if (containsRegex(line, "//\\s*#elifdef[ (]")) {// 5
					command = FSTDirectiveCommand.ELIFDEF;
				} else if (containsRegex(line, "//\\s*#elifndef[ (]")) {// 6
					command = FSTDirectiveCommand.ELIFNDEF;
				} else if (containsRegex(line, "//\\s*#else")) {// 7
					command = FSTDirectiveCommand.ELSE;
				} else if (containsRegex(line, "//\\s*#condition[ (]")) {// 8
					command = FSTDirectiveCommand.CONDITION;
				} else if (containsRegex(line, "//\\s*#define[ (]")) {// 9
					command = FSTDirectiveCommand.DEFINE;
				} else if (containsRegex(line, "//\\s*#undefine[ (]")) {// 10
					command = FSTDirectiveCommand.UNDEFINE;
				} else if (!containsRegex(line, "//\\s*#endif")) {// 11
					continue;
				}

				if (command == null) {
					if (!directivesStack.isEmpty()) {
						directivesStack.peek().setEndLine(i, line.length());
						while (!directivesStack.isEmpty()) {
							final FSTDirective parent = directivesStack.pop();
							if ((parent.getCommand() != FSTDirectiveCommand.ELIF) && (parent.getCommand() != FSTDirectiveCommand.ELIFDEF)
								&& (parent.getCommand() != FSTDirectiveCommand.ELIFNDEF) && (parent.getCommand() != FSTDirectiveCommand.ELSE)) {
								break;
							}
						}
					}
				} else {
					final FSTDirective directive = new FSTDirective();

					if (command == FSTDirectiveCommand.ELSE) {
						if (!directivesStack.isEmpty()) {
							directivesStack.peek().setEndLine(i, 0);
							directive.setFeatureNames(directivesStack.peek().getFeatureNames());
						}
					} else if ((command == FSTDirectiveCommand.ELIF) || (command == FSTDirectiveCommand.ELIFDEF) || (command == FSTDirectiveCommand.ELIFNDEF)) {
						if (!directivesStack.isEmpty()) {
							directivesStack.peek().setEndLine(i, 0);
						}
					}

					directive.setCommand(command);

					final Matcher m = patternCommands.matcher(line);
					line = m.replaceAll("").trim();

					if (directive.getFeatureNames() == null) {
						directive.setFeatureNames(getFeatureNames(line));
					}
					directive.setExpression(line);
					directive.setStartLine(i, 0);
					directive.setId(id++);
					if (command == FSTDirectiveCommand.CONDITION) {
						directive.setEndLine(lines.size());
						directive.setEndLine(lines.size(), 0);
					}
					if (directivesStack.isEmpty()) {
						directivesList.add(directive);
					} else {
						directivesStack.peek().addChild(directive);
					}

					if ((command != FSTDirectiveCommand.DEFINE) && (command != FSTDirectiveCommand.UNDEFINE)) {
						directivesStack.push(directive);
					}
				}
			}
		}
		return directivesList;
	}

	@Override
	protected boolean containsFeature(String text, String feature) {
		return contains(text, feature);
	}

	/**
	 * the Pattern: <ul> <li>set flag DOTALL</li> <li>match any characters</li> <li>match any whitespace characters</li> <li>match "//# if/...
	 * [operators]feature[operators]"</li> <li>match any further characters</li> </ul>
	 */
	public static boolean contains(String text, String feature) {
		final Pattern pattern = Pattern.compile(String.format(REGEX, feature));
		final Matcher matcher = pattern.matcher(text);
		return matcher.find();
	}

	@Override
	protected List<String> getFeatureNames(String expression) {
		String exp = expression.replaceAll("[()]", "");
		exp = exp.replaceAll("&&", "");
		exp = exp.replaceAll("!", "");
		exp = exp.replaceAll("\\|\\|", "");
		exp = exp.replaceAll("\\^", "");
		final List<String> featureNameList = new LinkedList<String>();
		for (final String s : exp.split(" ")) {
			if (s.trim().length() > 0) {
				featureNameList.add(s);
			}
		}
		return featureNameList;
	}

}
