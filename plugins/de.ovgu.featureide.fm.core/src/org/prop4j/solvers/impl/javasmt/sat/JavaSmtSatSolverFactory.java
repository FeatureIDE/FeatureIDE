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
package org.prop4j.solvers.impl.javasmt.sat;

import org.prop4j.solver.AbstractSolverFactory;
import org.prop4j.solver.IMusExtractor;
import org.prop4j.solver.IOptimizationSolver;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISmtProblem;
import org.prop4j.solvers.impl.javasmt.smt.JavaSmtSolver;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

/**
 * Concrete factory for JavaSmt Solvers for SAT and SMT problems.
 *
 * @author Joshua Sprey
 */
public class JavaSmtSatSolverFactory extends AbstractSolverFactory {

	public Solvers solver;
	public static final String ID = "org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolverFactory";

	@Override
	public String getId() {
		return ID;
	}

	public JavaSmtSatSolverFactory(Solvers solver) {
		this.solver = solver;
	}

	public JavaSmtSatSolverFactory() {
		solver = Solvers.SMTINTERPOL;
	}

	@Override
	public boolean initExtension() {
		return true;
	}

	@Override
	public String getDisplayName() {
		return "JavaSMT";
	}

	@Override
	public String getDisplayDescription() {
		return "JavaSMT is an interface for multiple SMT solver. JavaSMT can also be used to solve SAT problems.";
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.AbstractSolverFactory#isProvidingAnalysisSolver()
	 */
	@Override
	public boolean isProvidingAnalysisSolver() {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.SatSolverFactory#getSolver()
	 */
	@Override
	public ISatSolver getAnalysisSolver(ISatProblem problem) {
		return new JavaSmtSatSolver(problem, solver, null);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.AbstractSolverFactory#isProvidingExplanationSolver()
	 */
	@Override
	public boolean isProvidingExplanationSolver() {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.SatSolverFactory#getMusExtractor()
	 */
	@Override
	public IMusExtractor getExplanationSolver(ISatProblem problem) {
		return new JavaSmtSatMusExtractor(problem, solver, null);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.AbstractSolverFactory#isProvidingOptimizationSolver()
	 */
	@Override
	public boolean isProvidingOptimizationSolver() {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.AbstractSolverFactory#getOptimizationSolver(org.prop4j.solver.ISmtProblem)
	 */
	@Override
	public IOptimizationSolver getOptimizationSolver(ISmtProblem problem) {
		return new JavaSmtSolver(problem, Solvers.Z3, null);
	}

	@Override
	public AbstractSolverFactory getNewFactory() {
		return new JavaSmtSatSolverFactory();
	}

}
