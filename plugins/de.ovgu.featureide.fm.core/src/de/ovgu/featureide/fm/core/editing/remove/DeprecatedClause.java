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
package de.ovgu.featureide.fm.core.editing.remove;

import java.util.HashSet;

import org.prop4j.Literal;

import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.editing.remove.DeprecatedFeatureMap.DeprecatedFeature;

/**
 * Used by {@link FeatureRemover}.
 * 
 * @author Sebastian Krieter
 */
public class DeprecatedClause extends Clause {

	private int relevance;

	public static DeprecatedClause createClause(DeprecatedFeatureMap map, Literal[] newLiterals, String curFeature) {
		final HashSet<Literal> literalSet = new HashSet<>(newLiterals.length << 1);
		for (Literal literal : newLiterals) {
			if (!curFeature.equals(literal.var)) {
				final Literal negativeliteral = literal.clone();
				negativeliteral.flip();

				if (literalSet.contains(negativeliteral)) {
					return null;
				} else {
					literalSet.add(literal);
				}
			}
		}

		final DeprecatedClause clause = new DeprecatedClause(literalSet.toArray(new Literal[0]));
		clause.computeRelevance(map);
		return clause;
	}

	public static DeprecatedClause createClause(DeprecatedFeatureMap map, Literal[] newLiterals) {
		final HashSet<Literal> literalSet = new HashSet<>(newLiterals.length << 1);
		for (Literal literal : newLiterals) {
			final Literal negativeliteral = literal.clone();
			negativeliteral.flip();

			if (literalSet.contains(negativeliteral)) {
				return null;
			} else {
				literalSet.add(literal);
			}
		}

		final DeprecatedClause clause = new DeprecatedClause(literalSet.toArray(new Literal[0]));
		clause.computeRelevance(map);
		return clause;
	}

	public static DeprecatedClause createClause(DeprecatedFeatureMap map, Literal newLiteral) {
		final DeprecatedClause clause = new DeprecatedClause(new Literal[] { newLiteral });
		final DeprecatedFeature df = map.get(newLiteral.var);
		if (df != null) {
			clause.relevance++;
		}
		return clause;
	}

	private DeprecatedClause(Literal[] literals) {
		super(literals);
		this.relevance = 0;
	}

	private void computeRelevance(DeprecatedFeatureMap map) {
		for (Literal literal : literals) {
			final DeprecatedFeature df = map.get(literal.var);
			if (df != null) {
				relevance++;
				if (literal.positive) {
					df.incPositive();
				} else {
					df.incNegative();
				}
			}
		}
		if (relevance > 0 && relevance < literals.length) {
			map.incGlobalMixedClauseCount();
		}
	}

	public void delete(DeprecatedFeatureMap map) {
		if (literals != null && literals.length > 1) {
			for (Literal literal : literals) {
				final DeprecatedFeature df = map.get(literal.var);
				if (df != null) {
					if (literal.positive) {
						df.decPositive();
					} else {
						df.decNegative();
					}
				}
			}
			if (relevance > 0 && relevance < literals.length) {
				map.decGlobalMixedClauseCount();
			}
			literals = null;
		}
	}
	
	public int getRelevance() {
		return relevance;
	}

}
