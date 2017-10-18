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

import java.util.Collection;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.editing.cnf.CNFSolver;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;

/**
 * Removes features from a model while retaining dependencies of all other feature.
 *
 * @author Sebastian Krieter
 */
public class CFeatureRemover extends AFeatureRemover {

	public CFeatureRemover(Node cnf, Collection<String> features) {
		super(cnf, features);
	}

	public CFeatureRemover(Node cnf, Collection<String> features, boolean includeBooleanValues) {
		super(cnf, features, includeBooleanValues);
	}

	public CFeatureRemover(Node cnf, Collection<String> features, boolean includeBooleanValues, boolean regularCNF) {
		super(cnf, features, includeBooleanValues, regularCNF);
	}

	private void detectRedundantConstraintsComplex() {
		final CNFSolver solver = new CNFSolver(newClauseList, featureNameArray.length - 1);

		for (int i = 0; i < relevantPosIndex; i++) {
			final DeprecatedClause mainClause = relevantClauseList.get(i);
			if (isRemovable(solver, mainClause)) {
				removeRelevant(i--);
			} else {
				solver.addClause(mainClause);
			}
		}
	}

	private void detectRedundantConstraintsSimple() {
		for (int i = 0; i < relevantPosIndex; i++) {
			final DeprecatedClause mainClause = relevantClauseList.get(i);
			for (int j = i + 1; j < relevantPosIndex; j++) {
				final DeprecatedClause subClause = relevantClauseList.get(j);
				final Clause contained = Clause.contained(mainClause, subClause);
				if (contained != null) {
					if (subClause == contained) {
						removeRelevant(j--);
					} else {
						removeRelevant(i--);
						break;
					}
				}
			}
		}

		for (int i = 0; i < newRelevantDelIndex; i++) {
			final DeprecatedClause mainClause = newRelevantClauseList.get(i);
			for (int j = i + 1; j < newRelevantDelIndex; j++) {
				final DeprecatedClause subClause = newRelevantClauseList.get(j);
				final Clause contained = Clause.contained(mainClause, subClause);
				if (contained != null) {
					if (subClause == contained) {
						removeNewRelevant(j--);
					} else {
						removeNewRelevant(i--);
						break;
					}
				}
			}
		}

		for (int i = 0; i < relevantPosIndex; i++) {
			final DeprecatedClause mainClause = relevantClauseList.get(i);
			for (int j = 0; j < newRelevantDelIndex; j++) {
				final DeprecatedClause subClause = newRelevantClauseList.get(j);
				final Clause contained = Clause.contained(mainClause, subClause);
				if (contained != null) {
					if (subClause == contained) {
						removeNewRelevant(j--);
					} else {
						removeRelevant(i--);
						break;
					}
				}
			}
		}

	}

	@Override
	protected boolean detectRedundancy(DeprecatedFeature next) {
		final long estimatedClauseCount = next.getClauseCount();
		final int curClauseCountLimit = (int) Math.floor(localFactor * ((relevantNegIndex - relevantPosIndex) + newRelevantClauseList.size()));

		if ((estimatedClauseCount > maxClauseCountLimit) || (estimatedClauseCount > curClauseCountLimit)) {
			detectRedundantConstraintsSimple();
			detectRedundantConstraintsComplex();
			return true;
		}
		return false;
	}

	protected double localFactor = 1.0;
	protected double globalFactor = 1.0;
	protected int maxClauseCountLimit;

	@Override
	protected void prepareHeuristics() {
		localFactor = 1.1;
		globalFactor = 1.2;
		maxClauseCountLimit = (int) Math.floor(globalFactor * relevantClauseList.size());

		heuristic = new StaticMinimumClauseHeuristic(map, features.size());
	}

}
