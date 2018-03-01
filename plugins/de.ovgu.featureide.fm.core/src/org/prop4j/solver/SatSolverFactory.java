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
package org.prop4j.solver;

import org.prop4j.solver.impl.sat4j.Sat4JSatSolverFactory;

/**
 * Factory used to create solvers.
 *
 * @author Joshua Sprey
 */
public abstract class SatSolverFactory {

	/**
	 * Return a solver with a mus extractor interface
	 */
	public abstract IMusExtractor getMusExtractor(ISatProblem problem);

	/**
	 * Return a solver to solve sat querys
	 */
	public abstract ISatSolver getSolver(ISatProblem problem);

	/**
	 * Return a solver with a optimization interface
	 */
	public abstract IOptimizationSolver getOptimizationSolver(ISmtProblem problem);

	/**
	 * Returns the default factory for Sat4J solver
	 *
	 * @return
	 */
	public static SatSolverFactory getDefault() {
		return new Sat4JSatSolverFactory();
	}
}
