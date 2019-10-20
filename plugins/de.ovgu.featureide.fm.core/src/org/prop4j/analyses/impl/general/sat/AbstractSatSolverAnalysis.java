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

import org.prop4j.analyses.GeneralSolverAnalysis;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISolverProblem;

/**
 * Special abstract class for analysis that are only fitted for sat solvers.
 *
 * @author Joshua
 */
public abstract class AbstractSatSolverAnalysis<T> extends GeneralSolverAnalysis<T> {

	protected ISatSolver solver;

	/**
	 * Creates a new instance of an analysis with a given solver. It is no longer necessary to create a solver.
	 *
	 * @param solver The solver that should be used for this analysis.
	 */
	public AbstractSatSolverAnalysis(ISatSolver solver) {
		this.solver = solver;
	}

	/**
	 * Creates a new instance of an analysis with a given solver. It is necessary to create a solver by overriding
	 * {@link GeneralSolverAnalysis#initSolver(ISolverProblem)}.
	 *
	 * @param problemInstance A valid {@link ISatProblem} that should be used for the creation of the solver.
	 */
	public AbstractSatSolverAnalysis(ISatProblem instance) {
		this.solver = initSolver(instance);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.ISolverAnalysis#getSolver()
	 */
	@Override
	public ISatSolver getSolver() {
		return solver;
	}

	public abstract ISatSolver initSolver(ISatProblem problem);
}
