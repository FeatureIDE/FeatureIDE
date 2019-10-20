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
package org.prop4j.analyses.impl.general.sat;

import java.util.ArrayList;
import java.util.List;

import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.impl.SolverManager;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds false optional features without optimizations. Get as input pairs which contain the assumed false optional feature index and his negated parent index.
 * Was created and used for the evaluation against the optimized {@link ImplicationAnalysis}<br><br>
 *
 * Input: <br>FeaturA has Index: 2 <br>FeatureB has Index: 3 <br>FeatureA is parent of FeatureB and assumed to be FA<br>
 *
 * Result Input : {-Parent, FAFeature} => {-3, 2}
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class ClearImplicationAnalysis extends AbstractSatSolverAnalysis<List<int[]>> {

	private List<int[]> pairs;

	public ClearImplicationAnalysis(ISatSolver solver, List<int[]> pairs) {
		super(solver);
		this.pairs = pairs;
	}

	public ClearImplicationAnalysis(ISatProblem problem, List<int[]> pairs) {
		super(problem);
		this.pairs = pairs;
	}

	public void initParis(List<int[]> pairs) {
		this.pairs = pairs;
	}

	@Override
	protected List<int[]> analyze(IMonitor<List<int[]>> monitor) throws Exception {
		final List<int[]> resultList = new ArrayList<>();

		if (pairs == null) {
			return resultList;
		}

		monitor.checkCancel();

		for (final int[] pair : pairs) {
			for (final int i : pair) {
				try {
					// Push the assumption (Parent & -FAFeature)
					getSolver().push(getSolver().getProblem().getVariableAsNode(-i));
				} catch (final ContradictionException e) {
					// If contradiction then it is unsatisfiable => false optional
					resultList.add(pair);
					continue;
				}
			}
			switch (solver.isSatisfiable()) {
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
				solver.pop();
			}
		}
		return resultList;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.AbstractSatSolverAnalysis#initSolver(org.prop4j.solver.ISatProblem)
	 */
	@Override
	public ISatSolver initSolver(ISatProblem problem) {
		if (solver == null) {
			// Create new solver
			solver = SolverManager.getSelectedFeatureAttributeSolverFactory().getAnalysisSolver(problem);
		}
		return solver;
	}

}
