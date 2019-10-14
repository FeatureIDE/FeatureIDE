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
package org.prop4j.analyses.impl;

import java.util.HashMap;

import org.prop4j.analyses.AbstractSolverAnalysisFactory;
import org.prop4j.analyses.ISolverAnalysis;
import org.prop4j.analyses.impl.general.sat.ClearCoreDeadAnalysis;
import org.prop4j.analyses.impl.general.sat.CoreDeadAnalysis;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISolverProblem;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolver;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

/**
 * TODO SOLVER: replace the declaration of the solvers with property entry
 *
 * JavaSMT factory used to create analysis with JavaSMT appropriated solvers.
 *
 * @author Joshua Sprey
 */
public class JavaSmtSolverAnalysisFactory extends AbstractSolverAnalysisFactory {

	protected HashMap<String, Object> defaultConfiguration = new HashMap<String, Object>();

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.AbstractSolverAnalysisFactory#getDefaultConfiguration()
	 */
	@Override
	public HashMap<String, Object> getDefaultConfiguration() {
		return defaultConfiguration;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.AbstractSolverAnalysisFactory#setDefaultConfiguration(java.util.HashMap)
	 */
	@Override
	public void setDefaultConfiguration(HashMap<String, Object> map) {
		defaultConfiguration = map;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.ISolverAnalysisFactory#getAnalysis(java.lang.Object, org.prop4j.solver.ISolverProblem)
	 */
	@Override
	public ISolverAnalysis<?> getAnalysis(Class<?> analysisClass, ISolverProblem problem) {
//		if (analysisClass.equals(ValidAnalysis.class)) {
//			return getValidAnalyis(problem);
//		} else if (analysisClass.equals(CoreDeadAnalysis.class)) {
//			return getCoreDeadAnalysis(problem);
//		} else if (analysisClass.equals(ImplicationAnalysis.class)) {
//			return getImplicationAnalysis(problem);
//		} else if (analysisClass.equals(IndeterminedAnalysis.class)) {
//			return getIndeterminedAnalysis(problem);
//		} else if (analysisClass.equals(RedundantConstraintAnalysis.class)) {
//			return getRedundantConstraintAnalysis(problem);
//		} else if (analysisClass.equals(ConstraintsUnsatisfiableAnalysis.class)) {
//			return getConstraintsUnsatisfiableAnaylsis(problem);
//		} else if (analysisClass.equals(TautologicalConstraintAnalysis.class)) {
//			return getConstraintsTautologyAnaylsis(problem);
//		} else if (analysisClass.equals(FeatureAttributeRangeAnalysis.class)) {
//			return getFeatureAttributeRangeAnalysis(problem);
//		}
		if (analysisClass.equals(CoreDeadAnalysis.class)) {
			return getCoreDeadAnalysis(problem);
		} else if (analysisClass.equals(ClearCoreDeadAnalysis.class)) {
			return getClearCoreDeadAnalysis(problem);
		}
		return null;
	}

	private CoreDeadAnalysis getCoreDeadAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISatSolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
			return new CoreDeadAnalysis(solver);
		} else {
			return null;
		}
	}

	private ClearCoreDeadAnalysis getClearCoreDeadAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISatSolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
			return new ClearCoreDeadAnalysis(solver);
		} else {
			return null;
		}
	}

//	private ValidAnalysis getValidAnalyis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			final ISolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
//			return new ValidAnalysis(solver);
//		} else {
//			return null;
//		}
//	}
//
//	private ImplicationAnalysis getImplicationAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			final ISolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
//			return new ImplicationAnalysis(solver);
//		} else {
//			return null;
//		}
//	}
//
//	private IndeterminedAnalysis getIndeterminedAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			final ISolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
//			return new IndeterminedAnalysis(solver, null);
//		} else {
//			return null;
//		}
//	}
//
//	private RedundantConstraintAnalysis getRedundantConstraintAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			final ISolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
//			return new RedundantConstraintAnalysis(solver, this);
//		} else {
//			return null;
//		}
//	}
//
//	private ConstraintsUnsatisfiableAnalysis getConstraintsUnsatisfiableAnaylsis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			final ISolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
//			return new ConstraintsUnsatisfiableAnalysis(solver, this);
//		} else {
//			return null;
//		}
//	}
//
//	private TautologicalConstraintAnalysis getConstraintsTautologyAnaylsis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			final ISolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
//			return new TautologicalConstraintAnalysis(solver, this);
//		} else {
//			return null;
//		}
//	}
//
//	private FeatureAttributeRangeAnalysis getFeatureAttributeRangeAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISmtProblem) {
//			final ISmtSolver solver = new JavaSmtSolver((ISmtProblem) problem, Solvers.Z3, defaultConfiguration);
//			return new FeatureAttributeRangeAnalysis(solver);
//		} else {
//			return null;
//		}
//	}
//
//	private ClearCoreDeadAnalysis getAAACoreDeadAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			final ISolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
//			return new ClearCoreDeadAnalysis(solver);
//		} else {
//			return null;
//		}
//	}
//
//	private ClearImplicationAnalysis getAAAImplicationAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			final ISolver solver = new JavaSmtSatSolver((ISatProblem) problem, Solvers.SMTINTERPOL, defaultConfiguration);
//			return new ClearImplicationAnalysis(solver);
//		} else {
//			return null;
//		}
//	}
}
