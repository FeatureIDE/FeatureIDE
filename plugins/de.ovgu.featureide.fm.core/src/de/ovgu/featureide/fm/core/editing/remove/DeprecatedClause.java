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
package de.ovgu.featureide.fm.core.editing.remove;

import java.util.HashSet;

import de.ovgu.featureide.fm.core.editing.cnf.Clause;

/**
 * Used by {@link FeatureRemover}.
 *
 * @author Sebastian Krieter
 */
public class DeprecatedClause extends Clause {

	private int relevance;

	public static DeprecatedClause createClause(int[] newLiterals, int curFeature) {
		final HashSet<Integer> literalSet = new HashSet<>(newLiterals.length << 1);

		for (final int literal : newLiterals) {
			if (curFeature != Math.abs(literal)) {
				if (literalSet.contains(-literal)) {
					return null;
				} else {
					literalSet.add(literal);
				}
			}
		}

		return getClauseFromSet(literalSet);
	}

	public static DeprecatedClause createClause(int[] newLiterals, int curFeature, int[] helper) {
		int uniqueVarCount = newLiterals.length;
		for (int i = 0; i < newLiterals.length; i++) {
			final int l = newLiterals[i];
			final int index = Math.abs(l);
			if (index == curFeature) {
				newLiterals[i] = 0;
				uniqueVarCount--;
			} else {
				final int h = helper[index];
				if (h == 0) {
					helper[index] = l;
				} else {
					if (h != l) {
						for (int j = 0; j < i; j++) {
							helper[Math.abs(newLiterals[j])] = 0;
						}
						return null;
					} else {
						newLiterals[i] = 0;
						uniqueVarCount--;
					}
				}
			}
		}
		final int[] uniqueVarArray = new int[uniqueVarCount];
		int k = 0;
		for (int i = 0; i < newLiterals.length; i++) {
			final int l = newLiterals[i];
			helper[Math.abs(l)] = 0;
			if (l != 0) {
				uniqueVarArray[k++] = l;
			}
		}

		return new DeprecatedClause(uniqueVarArray);
	}

	public static DeprecatedClause createClause(int[] newLiterals) {
		final HashSet<Integer> literalSet = new HashSet<>(newLiterals.length << 1);

		for (final int literal : newLiterals) {
			if (literalSet.contains(-literal)) {
				return null;
			} else {
				literalSet.add(literal);
			}
		}

		return getClauseFromSet(literalSet);
	}

	private static DeprecatedClause getClauseFromSet(final HashSet<Integer> literalSet) {
		final int[] newLiterals = new int[literalSet.size()];
		int i = 0;
		for (final int lit : literalSet) {
			newLiterals[i++] = lit;
		}
		return new DeprecatedClause(newLiterals);
	}

	private DeprecatedClause(int[] literals) {
		super(literals);
		relevance = 0;
	}

	boolean computeRelevance(DeprecatedFeature[] map) {
		for (final int literal : literals) {
			final DeprecatedFeature df = map[Math.abs(literal)];
			if (df != null) {
				relevance++;
				if (literal > 0) {
					df.incPositive();
				} else {
					df.incNegative();
				}
			}
		}
		return ((relevance > 0) && (relevance < literals.length));
	}

	public boolean delete(DeprecatedFeature[] map) {
		if (literals.length > 1) {
			final boolean mixed = ((relevance > 0) && (relevance < literals.length));
			for (final int literal : literals) {
				final DeprecatedFeature df = map[Math.abs(literal)];
				if (df != null) {
					if (literal > 0) {
						df.decPositive();
					} else {
						df.decNegative();
					}
					if (mixed) {
						df.decMixed();
					}
				}
			}
			return mixed;
		} else {
			for (final int literal : literals) {
				final DeprecatedFeature df = map[Math.abs(literal)];
				if (df != null) {
					if (literal > 0) {
						df.decPositive();
					} else {
						df.decNegative();
					}
				}
			}
		}
		return false;
	}

	public int getRelevance() {
		return relevance;
	}

}
