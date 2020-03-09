/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.expression;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.dimacs.LineIterator;

/**
 * Reads and writes grouped propositional expressions in CNF.
 *
 * @author Sebastian Krieter
 */
public class ExpressionGroupFormat extends APersistentFormat<List<List<ClauseList>>> {

	public static final String ID = PluginID.PLUGIN_ID + ".format.expression." + ExpressionGroupFormat.class.getSimpleName();

	@Override
	public String write(List<List<ClauseList>> expressionGroups) {
		final StringBuilder sb = new StringBuilder();
		for (final List<? extends ClauseList> expressionGroup : expressionGroups) {
			sb.append("g ");
			sb.append(expressionGroup.size());
			sb.append(System.lineSeparator());
			for (final ClauseList expression : expressionGroup) {
				sb.append("e ");
				for (final LiteralSet literalSet : expression) {
					for (final int literal : literalSet.getLiterals()) {
						sb.append(literal);
						sb.append(" ");
					}
					sb.append("|");
				}
				sb.append(System.lineSeparator());
			}
		}
		return sb.toString();
	}

	@Override
	public ProblemList read(List<List<ClauseList>> expressionGroups, CharSequence source) {
		final ProblemList problemList = new ProblemList();
		expressionGroups.clear();
		ArrayList<ClauseList> expressionGroup = null;
		try (final BufferedReader reader = new BufferedReader(new StringReader(source.toString()))) {
			final LineIterator lineIterator = new LineIterator(reader);
			try {
				for (String line = lineIterator.get(); line != null; line = lineIterator.get()) {
					final char firstChar = line.charAt(0);
					switch (firstChar) {
					case 'g':
						final int groupSize = Integer.parseInt(line.substring(2).trim());
						expressionGroup = new ArrayList<>(groupSize);
						expressionGroups.add(expressionGroup);
						break;
					case 'e':
						if (expressionGroup == null) {
							throw new Exception("No group defined.");
						}
						final String expressionString = line.substring(2).trim();
						final String[] clauseStrings = expressionString.split("\\|");
						final PresenceCondition expression = new PresenceCondition();
						for (final String clauseString : clauseStrings) {
							final String[] literalStrings = clauseString.split("\\s+");
							final int[] literals = new int[literalStrings.length];
							int index = 0;
							for (final String literalString : literalStrings) {
								if (!literalString.isEmpty()) {
									final int literal = Integer.parseInt(literalString);
									literals[index++] = literal;
								}
							}
							expression.add(new LiteralSet(Arrays.copyOfRange(literals, 0, index)));
						}
						expressionGroup.add(expression);
						break;
					default:
						break;
					}
				}
			} catch (final Exception e) {
				problemList.add(new Problem(e, lineIterator.getLineCount()));
			}

		} catch (final IOException e) {
			Logger.logError(e);
		}
		return problemList;
	}

	@Override
	public String getSuffix() {
		return "expression";
	}

	@Override
	public ExpressionGroupFormat getInstance() {
		return this;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public String getName() {
		return "Expression Groups";
	}

}
