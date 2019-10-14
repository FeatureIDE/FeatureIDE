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
package org.prop4j.solver.impl.Ltms;

import org.prop4j.solver.AbstractSolverFactory;
import org.prop4j.solver.IMusExtractor;
import org.prop4j.solver.IOptimizationSolver;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISmtProblem;

/**
 * Concrete factory for Sat4J sat solver
 *
 * @author Joshua Sprey
 */
public class LtmsSatSolverFactory extends AbstractSolverFactory {

	public static final String ID = "org.prop4j.solver.impl.Ltms.LtmsSatSolverFactory";

	@Override
	public String getId() {
		return ID;
	}

	public LtmsSatSolverFactory() {}

	@Override
	public boolean initExtension() {
		return true;
	}

	@Override
	public String getDisplayName() {
		return "LTMS";
	}

	@Override
	public String getDisplayDescription() {
		return "The logic truth maintenence system is a boolean constraint propagator. It is fast but does not always provide a solution.";
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.AbstractSolverFactory#isProvidingAnalysisSolver()
	 */
	@Override
	public boolean isProvidingAnalysisSolver() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.AbstractSolverFactory#getAnalysisSolver(org.prop4j.solver.ISatProblem)
	 */
	@Override
	public ISatSolver getAnalysisSolver(ISatProblem problem) {
		throw new UnsupportedOperationException("Ltms cannot always find a solution, thus, it does not suit as an anylsis solver.");
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.AbstractSolverFactory#isProvidingExplanationSolver()
	 */
	@Override
	public boolean isProvidingExplanationSolver() {
		return true;
	}

	@Override
	public IMusExtractor getExplanationSolver(ISatProblem problem) {
		return new Ltms(problem, null);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.AbstractSolverFactory#isProvidingOptimizationSolver()
	 */
	@Override
	public boolean isProvidingOptimizationSolver() {
		return false;
	}

	@Override
	public IOptimizationSolver getOptimizationSolver(ISmtProblem problem) {
		throw new UnsupportedOperationException("Ltms does not support optimizing attributes.");
	}

	@Override
	public AbstractSolverFactory getNewFactory() {
		return new LtmsSatSolverFactory();
	}

}
