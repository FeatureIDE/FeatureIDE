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
package org.prop4j.analyses.impl.general;

import java.util.ArrayList;
import java.util.List;

import org.prop4j.analyses.GeneralSolverAnalysis;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISolver;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds false optional features. Get as input pairs which contain the assumed false optional feature index and his negated parent index.<br><br>
 *
 * Input: <br>FeaturA has Index: 2 <br>FeatureB has Index: 3 <br>FeatureA is parent of FeatureB and assumed to be FA<br>
 *
 * Result Input : {-Parent, FAFeature} => {-3, 2}
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class ClearImplicationAnalysis extends GeneralSolverAnalysis<List<int[]>> {

	private List<int[]> pairs;

	public ClearImplicationAnalysis(ISolver solver, List<int[]> pairs) {
		super(solver);
		this.pairs = pairs;
	}

	public ClearImplicationAnalysis(ISolver solver) {
		super(solver);
	}

	public void initParis(List<int[]> pairs) {
		this.pairs = pairs;
	}

	@Override
	public List<int[]> analyze(IMonitor monitor) {
		final List<int[]> resultList = new ArrayList<>();

		if (pairs == null) {
			return resultList;
		}

		monitor.checkCancel();

		for (final int[] pair : pairs) {
			for (final int i : pair) {
				try {
					// Push the assumption (Parent & -FAFeature)
					solverPush(getLiteralFromIndex(-i));
				} catch (final ContradictionException e) {
					// If contradiction then it is unsatisfiable => false optional
					resultList.add(pair);
					continue;
				}
			}
			switch (solverSatisfiable()) {
			case FALSE:
				// Feature is false optional add to result list
				resultList.add(pair);
				break;
			case TIMEOUT:
			case TRUE:
				// Feature is not false optional
				break;
			}
			// Remove pushed assumptions from the solver
			for (int i = 0; i < pair.length; i++) {
				solverPop();
			}
		}
		return resultList;
	}
}
