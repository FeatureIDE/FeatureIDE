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

import de.ovgu.featureide.fm.core.IExtension;

/**
 * This factory can be extended to add solvers to FeatureIDE.
 *
 * @author Joshua Sprey
 */
public abstract class AbstractSolverFactory implements IExtension {

	public static String extensionPointID = "SolverFactory";

	public static String extensionID = "solverFactory";

	/**
	 * The name that should be displayed when handling the solver settings.
	 */
	public abstract String getDisplayName();

	/**
	 * The information that should be displayed when handling the solver settings.
	 */
	public abstract String getDisplayDescription();

	/**
	 * Does the factory provides an explanation solver (SAT) that can be used by FeatureIDE to explain anomalies in the feature model.
	 */
	public abstract boolean isProvidingExplanationSolver();

	/**
	 * Does the factory provides an analysis solver (SAT) that can be used by FeatureIDE to detect anomalies in the feature model.
	 */
	public abstract boolean isProvidingAnalysisSolver();

	/**
	 * Does the factory provides an optimization solver (SMT) that can be used by FeatureIDE to optimize attributes.
	 */
	public abstract boolean isProvidingOptimizationSolver();

	/**
	 * Return a solver with a mus extractor interface
	 */
	public abstract IMusExtractor getExplanationSolver(ISatProblem problem);

	/**
	 * Return a solver to solve sat querys
	 */
	public abstract ISatSolver getAnalysisSolver(ISatProblem problem);

	/**
	 * Return a solver with a optimization interface
	 */
	public abstract IOptimizationSolver getOptimizationSolver(ISmtProblem problem);

	/**
	 * Returns the default factory used by FeatureIDE.
	 */
	public static AbstractSolverFactory getDefault() {
		return new Sat4JSatSolverFactory();
	}

	/**
	 * Returns a new instance of the solver factory.
	 */
	public abstract AbstractSolverFactory getNewFactory();
}
