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

import org.prop4j.analyses.AbstractSatSolverAnalysis;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.impl.SolverManager;
import org.prop4j.solver.impl.SolverUtils;

import de.ovgu.featureide.fm.core.base.util.RingList;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds false optional features without optimizations. Get as input pairs which contain the assumed false optional feature index and his negated parent
 * index.<br><br>
 *
 * Input: <br>FeaturA has Index: 2 <br>FeatureB has Index: 3 <br>FeatureA is parent of FeatureB and assumed to be FA<br>
 *
 * Result Input : List[{-Parent, FAFeature}] => List[{-3, 2}]<br><br>
 *
 * For this optimization we save the intermediate solutions and before checking a new pair of (Parent & Possible-FA-Feature), we perform a lookup in the saved
 * solution and compare the assignment for both features. If an assignment of the following for can be found:
 *
 * <li>Parent=TRUE and FAFeature=FALSE</li>
 *
 * then possible false-optional feature is not false-optional.
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class ImplicationAnalysis extends AbstractSatSolverAnalysis<List<int[]>> {

	private List<int[]> pairs;

	public ImplicationAnalysis(ISatSolver solver, List<int[]> pairs) {
		super(solver);
		this.pairs = pairs;
	}

	public ImplicationAnalysis(ISatProblem problem, List<int[]> pairs) {
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

		final RingList<int[]> solutionList = new RingList<>(Math.min(pairs.size(), ISolver.MAX_SOLUTION_BUFFER));
		monitor.checkCancel();

		getSolver().isSatisfiable();
		final int[] model1 = SolverUtils.getIntModel(getSolver().getSolution());

		if (model1 != null) {
			solutionList.add(model1);

			pairLoop: for (final int[] pair : pairs) {
				monitor.checkCancel();
				for (final int[] is : solutionList) {
					// if any solution was found => not FO
					if (containsNonFOAssignment(is, pair)) {
						continue pairLoop;
					}
				}
				monitor.checkCancel();
				for (final int i : pair) {
					try {
						getSolver().push(getLiteralFromIndex(-i));
					} catch (final ContradictionException e) {
						// Is unsatisfiable => false optional
						resultList.add(pair);
					}
				}
				switch (getSolver().isSatisfiable()) {
				case FALSE:
					resultList.add(pair);
					break;
				case TIMEOUT:
					break;
				case TRUE:
					solutionList.add(SolverUtils.getIntModel(solver.getSolution()));
					break;
				}
				for (int i = 0; i < pair.length; i++) {
					getSolver().pop();
				}
			}
		}
		return resultList;
	}

	/**
	 *
	 * @param solution
	 * @param pair (-Parent, P-FO-Feature)
	 * @return
	 */
	private boolean containsNonFOAssignment(int[] solution, int[] pair) {
		boolean parent = false;
		boolean feature = false;
		for (final int i : solution) {
			// Contains parent = TRUE
			if ((Math.abs(i) == Math.abs(pair[0])) && (i >= 0)) {
				parent = true;
			}
			// Contains feature = FALSE
			if ((Math.abs(i) == Math.abs(pair[1])) && (i < 0)) {
				feature = true;
			}
		}
		if (parent && feature) {
			return true;
		} else {
			return false;
		}
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
