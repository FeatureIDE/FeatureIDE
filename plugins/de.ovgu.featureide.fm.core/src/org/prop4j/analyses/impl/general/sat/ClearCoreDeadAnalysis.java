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
import org.prop4j.solver.impl.SolverManager;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features without using any optimizations. Was created and used for evaluation against the optimized version of the analysis. The
 * optimized version is implemented in {@link CoreDeadAnalysis}
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class ClearCoreDeadAnalysis extends AbstractSatSolverAnalysis<LiteralSet> {

	public ClearCoreDeadAnalysis(ISatProblem problem) {
		super(problem);
	}

	public ClearCoreDeadAnalysis(ISatSolver solver) {
		super(solver);
	}

	@Override
	public LiteralSet analyze(IMonitor<LiteralSet> monitor) throws Exception {
		final List<Integer> features = new ArrayList<>();

		// Detect Core
		for (int i = 1; i <= getSolver().getProblem().getNumberOfVariables(); i++) {
			final int varX = i;
			try {
				getSolver().push(getLiteralFromIndex(-varX));
			} catch (final ContradictionException e1) {
				// If contradiction then it is unsatisfiable => core feature
				try {
					getSolver().push(getLiteralFromIndex(varX));
				} catch (final ContradictionException e) {
					FMCorePlugin.getDefault().logError(e);
				}
				// Memorize varX as core feature
				features.add(varX);
			}
			switch (getSolver().isSatisfiable()) {
			case FALSE:
				// If unsatisfiable => core feature
				getSolver().pop();
				try {
					getSolver().push(getLiteralFromIndex(varX));
				} catch (final ContradictionException e) {
					FMCorePlugin.getDefault().logError(e);
				}
				// Memorize varX as core feature
				features.add(varX);
				break;
			case TIMEOUT:
				getSolver().pop();
				reportTimeout();
				break;
			case TRUE:
				getSolver().pop();
				break;
			}

		}
		// Detect Dead
		for (int i = 1; i <= getSolver().getProblem().getNumberOfVariables(); i++) {
			final int varX = -i;
			try {
				getSolver().push(getLiteralFromIndex(-varX));
			} catch (final ContradictionException e1) {
				// If contradiction then it is unsatisfiable => dead feature
				try {
					getSolver().push(getLiteralFromIndex(varX));
				} catch (final ContradictionException e) {
					FMCorePlugin.getDefault().logError(e);
				}
				// Memorize varX as dead feature, negation is not needed because varX was defined negatively
				features.add(varX);
			}
			switch (getSolver().isSatisfiable()) {
			case FALSE:
				// If unsatisfiable => dead feature
				getSolver().pop();
				try {
					getSolver().push(getLiteralFromIndex(varX));
				} catch (final ContradictionException e) {
					FMCorePlugin.getDefault().logError(e);
				}
				// Memorize varX as dead feature, negation is not needed because varX was defined negatively
				features.add(varX);
				break;
			case TIMEOUT:
				getSolver().pop();
				reportTimeout();
				break;
			case TRUE:
				getSolver().pop();
				break;
			}
		}
		final int[] result = new int[features.size()];
		for (int i = 0; i < result.length; i++) {
			result[i] = features.get(i);
		}
		return new LiteralSet(result);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.ISolverAnalysis#initSolver(org.prop4j.solver.ISolverProblem)
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
