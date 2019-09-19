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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.TreeSet;

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

/**
 *
 * @author Sebastian Krieter
 */
public class TWiseCombiner {

	/**
	 * Converts a set of single literals into a grouped expression list.
	 *
	 * @param literalSet the literal set
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertLiterals(LiteralSet literalSet) {
		return convertGroupedLiterals(Arrays.asList(literalSet));
	}

	/**
	 * Converts a grouped set of single literals into a grouped expression list.
	 *
	 * @param groupedLiterals the grouped literal sets
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertGroupedLiterals(List<LiteralSet> groupedLiterals) {
		final List<List<ClauseList>> groupedExpressions = new ArrayList<>(groupedLiterals.size());
		for (final LiteralSet literalSet : groupedLiterals) {
			final List<ClauseList> arrayList = new ArrayList<>(literalSet.size());
			groupedExpressions.add(arrayList);
			for (final Integer literal : literalSet.getLiterals()) {
				final ClauseList clauseList = new ClauseList(1);
				clauseList.add(new LiteralSet(literal));
				arrayList.add(clauseList);
			}
		}
		return groupedExpressions;
	}

	/**
	 * Converts an expression list into a grouped expression set with a single group.
	 *
	 * @param expressions the expression list
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertExpressions(List<ClauseList> expressions) {
		return Arrays.asList(expressions);
	}

	private final VecInt lits = new VecInt();
	private final int[] features;

	public TWiseCombiner(int numberOfVariables) {
		features = new int[numberOfVariables + 1];
	}

	public boolean combineConditions(PresenceCondition[] conditionArray, ClauseList combinedCondition) {
		return combineConditions(conditionArray, 0, combinedCondition);
	}

	private boolean combineConditions(PresenceCondition[] conditionArray, int t, ClauseList combinedCondition) {
		if (t == conditionArray.length) {
			final int[] combinedLiteralsArray = Arrays.copyOfRange(lits.toArray(), 0, lits.size());
			combinedCondition.add(new LiteralSet(combinedLiteralsArray));
		} else {
			clauseLoop: for (final LiteralSet clause : conditionArray[t]) {
				final int[] literals = clause.getLiterals();
				for (int i = 0; i < literals.length; i++) {
					final int literal = literals[i];
					final int var = Math.abs(literal);
					final int x = features[var];
					if ((x != 0) && ((literal ^ x) < 0)) {
						for (i--; i >= 0; i--) {
							final int undoLiteral = literals[i];
							final int var2 = Math.abs(undoLiteral);
							final int y = features[var2];
							final int y2 = y - ((undoLiteral >>> 31) == 0 ? 1 : -1);
							features[var2] = y2;
							if (y2 == 0) {
								lits.pop();
							}
						}
						continue clauseLoop;
					} else {
						features[var] = x + ((literal >>> 31) == 0 ? 1 : -1);
						if (x == 0) {
							lits.push(literal);
						}
					}
				}
				if (!combineConditions(conditionArray, t + 1, combinedCondition)) {
					return false;
				}
				for (int i = 0; i < literals.length; i++) {
					final int literal = literals[i];
					final int var = Math.abs(literal);
					final int y = features[var];
					final int y2 = y - ((literal >>> 31) == 0 ? 1 : -1);
					features[var] = y2;
					if (y2 == 0) {
						lits.pop();
					}
				}
			}
		}
		return true;
	}

	private boolean combineIteratively(PresenceCondition[] conditionArray, ClauseList combinedCondition) {
		final int[] clauseIndex = new int[conditionArray.length];
		clauseIndex[0] = -1;

		int i = 0;
		loop: while (i < clauseIndex.length) {
			for (i = 0; i < clauseIndex.length; i++) {
				final int cindex = clauseIndex[i];
				if (cindex == (conditionArray[i].size() - 1)) {
					clauseIndex[i] = 0;
				} else {
					clauseIndex[i] = cindex + 1;

					final LiteralSet literalSet = getCombinationLiterals(clauseIndex, conditionArray);
					if (literalSet != null) {
						combinedCondition.add(literalSet);
						continue loop;
					}
				}
			}
		}
		return true;
	}

	private LiteralSet getCombinationLiterals(final int[] clauseIndex, final PresenceCondition[] clauseListArray) {
		final TreeSet<Integer> newLiteralSet = new TreeSet<>();
		for (int j = 0; j < clauseIndex.length; j++) {
			for (final int literal : clauseListArray[j].get(clauseIndex[j]).getLiterals()) {
				if (newLiteralSet.contains(-literal)) {
					return null;
				} else {
					newLiteralSet.add(literal);
				}
			}
		}

		final int[] combinationLiterals = new int[newLiteralSet.size()];
		int j = 0;
		for (final Integer literal : newLiteralSet) {
			combinationLiterals[j++] = literal;
		}
		final LiteralSet literalSet = new LiteralSet(combinationLiterals);
		return literalSet;
	}

	private boolean combineConditions3(PresenceCondition[] conditionArray, int t, ClauseList combinedCondition) {
		if (t == conditionArray.length) {
			final int[] combinedLiteralsArray = Arrays.copyOfRange(lits.toArray(), 0, lits.size());
			combinedCondition.add(new LiteralSet(combinedLiteralsArray));
		} else {
			clauseLoop: for (final LiteralSet clause : conditionArray[t]) {
				final int[] literals = clause.getLiterals();
				for (int i = 0; i < literals.length; i++) {
					final int literal = literals[i];
					final int var = Math.abs(literal);
					final int x = features[var];
					if ((x != 0) && ((literal ^ x) < 0)) {
						for (i--; i >= 0; i--) {
							final int undoLiteral = literals[i];
							final int var2 = Math.abs(undoLiteral);
							final int y = features[var2];
							final int y2 = y - ((undoLiteral >>> 31) == 0 ? 1 : -1);
							features[var2] = y2;
							if (y2 == 0) {
								lits.pop();
							}
						}
						continue clauseLoop;
					} else {
						features[var] = x + ((literal >>> 31) == 0 ? 1 : -1);
						if (x == 0) {
							lits.push(literal);
						}
					}
				}
				if (!combineConditions(conditionArray, t + 1, combinedCondition)) {
					return false;
				}
				for (int i = 0; i < literals.length; i++) {
					final int literal = literals[i];
					final int var = Math.abs(literal);
					final int y2 = features[var] - ((literal >>> 31) == 0 ? 1 : -1);
					features[var] = y2;
					if (y2 == 0) {
						lits.pop();
					}
				}
			}
		}
		return true;
	}

	private boolean combineConditions2(PresenceCondition[] conditionArray, int t, ClauseList combinedCondition) {
		if (t == conditionArray.length) {
			if (combinedCondition.size() >= 1) {
				return false;
			}
			final int[] combinedLiteralsArray = Arrays.copyOfRange(lits.toArray(), 0, lits.size());
			combinedCondition.add(new LiteralSet(combinedLiteralsArray));
		} else {
			clauseLoop: for (final LiteralSet clause : conditionArray[t]) {
				final int[] literals = clause.getLiterals();
				for (int i = 0; i < literals.length; i++) {
					final int literal = literals[i];
					final int var = Math.abs(literal);
					final int x = features[var];
					if ((x != 0) && ((literal ^ x) < 0)) {
						for (i--; i >= 0; i--) {
							final int undoLiteral = literals[i];
							final int var2 = Math.abs(undoLiteral);
							final int y = features[var2];
							final int y2 = y - ((undoLiteral >>> 31) == 0 ? 1 : -1);
							features[var2] = y2;
							if (y2 == 0) {
								lits.pop();
							}
						}
						continue clauseLoop;
					} else {
						features[var] = x + ((literal >>> 31) == 0 ? 1 : -1);
						if (x == 0) {
							lits.push(literal);
						}
					}
				}
				if (!combineConditions(conditionArray, t + 1, combinedCondition)) {
					return false;
				}
				for (int i = 0; i < literals.length; i++) {
					final int literal = literals[i];
					final int var = Math.abs(literal);
					final int y2 = features[var] - ((literal >>> 31) == 0 ? 1 : -1);
					features[var] = y2;
					if (y2 == 0) {
						lits.pop();
					}
				}
			}
		}
		return true;
	}

}
