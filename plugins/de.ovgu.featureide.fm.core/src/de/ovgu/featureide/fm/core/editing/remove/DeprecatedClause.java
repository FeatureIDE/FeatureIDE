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

		for (int literal : newLiterals) {
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

	public static DeprecatedClause createClause(int[] newLiterals) {
		final HashSet<Integer> literalSet = new HashSet<>(newLiterals.length << 1);

		for (int literal : newLiterals) {
			if (literalSet.contains(-literal)) {
				return null;
			} else {
				literalSet.add(literal);
			}
		}

		return getClauseFromSet(literalSet);
	}

	private static DeprecatedClause getClauseFromSet(final HashSet<Integer> literalSet) {
		int[] newLiterals = new int[literalSet.size()];
		int i = 0;
		for (int lit : literalSet) {
			newLiterals[i++] = lit;
		}
		return new DeprecatedClause(newLiterals);
	}

	public static DeprecatedClause createClause(DeprecatedFeature[] map, int newLiteral) {
		final DeprecatedClause clause = new DeprecatedClause(new int[] { newLiteral });
		final DeprecatedFeature df = map[Math.abs(newLiteral)];
		if (df != null) {
			clause.relevance++;
		}
		return clause;
	}

	private DeprecatedClause(int[] literals) {
		super(literals);
		this.relevance = 0;
	}

	boolean computeRelevance(DeprecatedFeature[] map) {
		for (int literal : literals) {
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
		return (relevance > 0 && relevance < literals.length);
	}

	public boolean delete(DeprecatedFeature[] map) {
		if (literals != null && literals.length > 1) {
			for (int literal : literals) {
				final DeprecatedFeature df = map[Math.abs(literal)];
				if (df != null) {
					if (literal > 0) {
						df.decPositive();
					} else {
						df.decNegative();
					}
				}
			}
			return (relevance > 0 && relevance < literals.length);
		}
		return false;
	}

	public int getRelevance() {
		return relevance;
	}

}
