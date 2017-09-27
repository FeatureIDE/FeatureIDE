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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.editing.cnf.CNFSolver;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.editing.cnf.ICNFSolver;

/**
 * Removes features from a model while retaining dependencies of all other feature.
 *
 * @author Sebastian Krieter
 */
public class CFeatureRemover23 extends AFeatureRemover {

	private ICNFSolver newSolver;

	private boolean first = false;

	public CFeatureRemover23(Node cnf, Collection<String> features) {
		super(cnf, features);
	}

	public CFeatureRemover23(Node cnf, Collection<String> features, boolean includeBooleanValues) {
		super(cnf, features, includeBooleanValues);
	}

	public CFeatureRemover23(Node cnf, Collection<String> features, boolean includeBooleanValues, boolean regularCNF) {
		super(cnf, features, includeBooleanValues, regularCNF);
	}

	@Override
	protected boolean detectRedundancy(DeprecatedFeature nextFeature) {
		if (nextFeature.getClauseCount() > 0) {

			final List<DeprecatedClause> relevantSubList = relevantClauseList.subList(0, relevantPosIndex);
			Collections.sort(newRelevantClauseList.subList(0, newRelevantDelIndex), lengthComparator);

			final ArrayList<Clause> clauseList = new ArrayList<>(newClauseList.size() + relevantSubList.size());
			clauseList.addAll(newClauseList);
			clauseList.addAll(relevantSubList);
			final CNFSolver solver = new CNFSolver(clauseList, featureNameArray.length - 1);

			// SAT NewRelevant
			for (int i = newRelevantDelIndex - 1; i >= 0; --i) {
				final DeprecatedClause curClause = newRelevantClauseList.get(i);
				if (isRemovable(solver, curClause)) {
					removeNewRelevant(i);
				} else {
					solver.addClause(curClause);
				}
			}

			return true;
		}
		return false;
	}

	@Override
	protected void addNewClauses(DeprecatedFeature nextFeature) {
		if (nextFeature.getClauseCount() > 0) {
			Collections.sort(newNewClauseList, lengthComparator);

			for (int i = newNewClauseList.size() - 1; i >= 0; --i) {
				final DeprecatedClause clause = newNewClauseList.get(i);
				if (isRemovable(newSolver, clause)) {
					deleteClause(clause);
				} else {
					newSolver.addClause(clause);
					newClauseList.add(clause);
				}
			}
			newNewClauseList.clear();
		}
	}

	@Override
	protected void preRedundancyCheck(DeprecatedFeature nextFeature) {
		if (first && (nextFeature.getClauseCount() > 0)) {
			final String s = heuristic.size() + ": " + nextFeature.getFeature() + " | Removing Old Rel: " + relevantClauseList.size();
			System.err.print(s);
			first = false;
			Collections.sort(relevantClauseList, lengthComparator);

			addNewClauses(nextFeature);
			final CNFSolver solver = new CNFSolver(newClauseList, featureNameArray.length - 1);

			// SAT Relevant
			for (int i = relevantPosIndex - 1; i >= 0; --i) {
				final DeprecatedClause mainClause = relevantClauseList.get(i);
				if (isRemovable(solver, mainClause)) {
					removeRelevant(i);
				} else {
					solver.addClause(mainClause);
				}
			}
			deleteOldRelevantClauses();

			relevantPosIndex = relevantClauseList.size();
			relevantNegIndex = relevantClauseList.size();

			System.err.println(" Done.");
		}
	}

	@Override
	protected void prepareHeuristics() {
		heuristic = new MinimumClauseHeuristic(map, features.size());
		// heuristic = new StaticMinimumClauseHeuristic(map, features.size());
		first = true;
		newSolver = new CNFSolver(newClauseList, featureNameArray.length - 1);
	}

	@Override
	protected void release() {
		super.release();

		if (newSolver != null) {
			newSolver.reset();
		}
	}

}
