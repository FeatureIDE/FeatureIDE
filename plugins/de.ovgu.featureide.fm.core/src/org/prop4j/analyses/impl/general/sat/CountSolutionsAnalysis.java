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

import org.prop4j.Literal;
import org.prop4j.Or;
import org.prop4j.analyses.AbstractSatSolverAnalysis;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.SatResult;
import org.prop4j.solver.impl.SolverManager;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * This analysis counts the solution of the solver by computing different assignments iteratively.
 *
 * TODO SOLVERS rewrite with clause and literal set implementation
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class CountSolutionsAnalysis extends AbstractSatSolverAnalysis<Long> {

	public CountSolutionsAnalysis(ISatProblem problem) {
		super(problem);
	}

	public CountSolutionsAnalysis(ISatSolver solver) {
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
	protected Long analyze(IMonitor<Long> monitor) throws Exception {
		// TODO SOLVER Sebastian, what is a global timeout?
		// solver.setGlobalTimeout(true);
		long solutionCount = 0;
		SatResult hasSolution = solver.isSatisfiable();
		while (hasSolution == SatResult.TRUE) {
			solutionCount++;
			final Object[] solution = solver.getSolution();
			try {
				final Or clause = new Or();
				final Literal[] literals = new Literal[solution.length];
				for (int i = 0; i < solution.length; i++) {
					if (solution[i] instanceof Integer) {
						final int value = (int) solution[i];
						final Literal lit = new Literal(solver.getProblem().getVariableOfIndex(value), value >= 0 ? true : false);
						literals[i] = lit;
					}
				}
				clause.setChildren(literals);
				solver.push(clause);
			} catch (final ContradictionException e) {
				break;
			}
			hasSolution = solver.isSatisfiable();
		}
		return hasSolution == SatResult.TIMEOUT ? -(solutionCount + 1) : solutionCount;
	}
}
