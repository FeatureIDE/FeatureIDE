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

import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.SatResult;
import org.prop4j.solver.impl.SolverManager;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * A general SAT analysis to check weather the given problem is satisfiable.
 *
 * @author Joshua Sprey
 * @author Sebastian Krieter
 */
public class HasSolutionAnalysis extends AbstractSatSolverAnalysis<Boolean> {

	public HasSolutionAnalysis(ISatProblem instance) {
		super(instance);
	}

	public HasSolutionAnalysis(ISatSolver solver) {
		super(solver);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.GeneralSolverAnalysis#analyze(de.ovgu.featureide.fm.core.job.monitor.IMonitor)
	 */
	@Override
	public ISatSolver initSolver(ISatProblem problem) {
		if (solver == null) {
			// Create new solver
			solver = SolverManager.getSelectedFeatureAttributeSolverFactory().getAnalysisSolver(problem);
		}
		return solver;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.GeneralSolverAnalysis#analyze(de.ovgu.featureide.fm.core.job.monitor.IMonitor)
	 */
	@Override
	protected Boolean analyze(IMonitor<Boolean> monitor) throws Exception {
		final SatResult hasSolution = solver.isSatisfiable();
		switch (hasSolution) {
		case FALSE:
			return false;
		case TIMEOUT:
			reportTimeout();
			return false;
		case TRUE:
			return true;
		default:
			throw new AssertionError(hasSolution);
		}
	}

}
