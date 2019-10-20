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
package org.prop4j.analyses.impl.smt;

import org.prop4j.Literal;
import org.prop4j.solver.IOptimizationSolver;
import org.prop4j.solver.ISmtProblem;
import org.prop4j.solver.ISmtSolver;
import org.prop4j.solver.impl.SolverManager;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds the minimum and maximum value of a Term. As example we have the following expression:<br><br>
 *
 * <code> (Price + 233) > -17</code><br><br>
 *
 * If you want to evaluate the maximum and minimum value for the variabe <code>Price</code> you need to pass the {@link Literal} object to the analysis. The
 * variable of interest can be set via {@link FeatureAttributeRangeAnalysis#setVariable(Object)} or can be passed on the constructor
 * {@link #FeatureAttributeRangeAnalysis(ISmtProblem, Literal)}.
 *
 * @author Joshua Sprey
 */
public class FeatureAttributeRangeAnalysis extends AbstractSmtSolverAnalysis<Object[]> {

	/** The variable of interest */
	private Literal variable;

	public FeatureAttributeRangeAnalysis(ISmtSolver solver, Literal variableOfInterest) {
		super(solver);
		variable = variableOfInterest;
	}

	public FeatureAttributeRangeAnalysis(ISmtProblem instance, Literal variableOfInterest) {
		super(instance);
		variable = variableOfInterest;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.GeneralSolverAnalysis#analyze(de.ovgu.featureide.fm.core.job.monitor.IMonitor)
	 */
	@Override
	protected Object[] analyze(IMonitor<Object[]> monitor) throws Exception {

		if ((variable == null) || !(getSolver() instanceof IOptimizationSolver)) {
			return null;
		}
		final IOptimizationSolver solver = (IOptimizationSolver) getSolver();
		final Object[] result = new Object[2];
		getSolver().findSolution();
		result[0] = solver.minimum(variable);
		result[1] = solver.maximum(variable);

		return result;
	}

	/**
	 * Sets the variable of interest. As example we have the following expression:<br><br>
	 *
	 * <code> (Price + 233) > -17</code><br><br>
	 *
	 * If you want to evaluate the maximum and minimum value for the variabe <code>Price</code> you need to pass the Literal object for <code>Price</code>.
	 *
	 * @param variable The variable to compute the maximum and minimum of.
	 */
	public void setVariable(Literal variable) {
		this.variable = variable;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.impl.smt.AbstractSmtSolverAnalysis#initSolver(org.prop4j.solver.ISmtProblem)
	 */
	@Override
	public ISmtSolver initSolver(ISmtProblem problem) {
		if (solver == null) {
			// Create new solver
			solver = SolverManager.getSelectedFeatureAttributeSolverFactory().getOptimizationSolver(problem);
		}
		return solver;
	}
}
