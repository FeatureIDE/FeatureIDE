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
import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISolverProblem;
import org.prop4j.solver.impl.sat4j.Sat4JSatSolver;

/**
 * Default factory used to create analysis with their appropriate solver.
 *
 * @author Joshua Sprey
 */
public class Sat4JSolverAnalysisFactory extends AbstractSolverAnalysisFactory {

	private HashMap<String, Object> defaultConfiguration = new HashMap<String, Object>();

	public Sat4JSolverAnalysisFactory() {
		defaultConfiguration.put(AbstractSatSolver.CONFIG_TIMEOUT, 10_000);
		defaultConfiguration.put(Sat4JSatSolver.CONFIG_DB_SIMPLIFICATION_ALLOWED, true);
		defaultConfiguration.put(Sat4JSatSolver.CONFIG_VERBOSE, false);
	}

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
//			return getConstraintsUnsatisfiableAnaylsis(problem);// Start AAAAAAAAAAAAAAAAAAAAAAS
//		} else if (analysisClass.equals(TautologicalConstraintAnalysis.class)) {
//			return getConstraintsTautologyAnaylsis(problem);
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
			try {
				final ISatSolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
				return new CoreDeadAnalysis(solver);
			} catch (final ContradictionException e) {
				return null;
			}
		} else {
			return null;
		}
	}

	private ClearCoreDeadAnalysis getClearCoreDeadAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			try {
				final ISatSolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
				return new ClearCoreDeadAnalysis(solver);
			} catch (final ContradictionException e) {
				return null;
			}
		} else {
			return null;
		}
	}
//
//	private ValidAnalysis getValidAnalyis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			try {
//				final ISolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
//				return new ValidAnalysis(solver);
//			} catch (final ContradictionException e) {
//				return null;
//			}
//		} else {
//			return null;
//		}
//	}
//
//	private ImplicationAnalysis getImplicationAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			try {
//				final ISolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
//				return new ImplicationAnalysis(solver);
//			} catch (final ContradictionException e) {
//				return null;
//			}
//		} else {
//			return null;
//		}
//	}
//
//	private IndeterminedAnalysis getIndeterminedAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			try {
//				final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
//				return new IndeterminedAnalysis(solver, null);
//			} catch (final ContradictionException e) {
//				return null;
//			}
//		} else {
//			return null;
//		}
//	}
//
//	private RedundantConstraintAnalysis getRedundantConstraintAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			try {
//				final ISolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
//				return new RedundantConstraintAnalysis(solver, this);
//			} catch (final ContradictionException e) {
//				return null;
//			}
//		} else {
//			return null;
//		}
//	}
//
//	private ConstraintsUnsatisfiableAnalysis getConstraintsUnsatisfiableAnaylsis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			try {
//				final ISolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
//				return new ConstraintsUnsatisfiableAnalysis(solver, this);
//			} catch (final ContradictionException e) {
//				return null;
//			}
//		} else {
//			return null;
//		}
//	}
//
//	private TautologicalConstraintAnalysis getConstraintsTautologyAnaylsis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			try {
//				final ISolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
//				return new TautologicalConstraintAnalysis(solver, this);
//			} catch (final ContradictionException e) {
//				return null;
//			}
//		} else {
//			return null;
//		}
//	}
//
//	private ClearCoreDeadAnalysis getAAACoreDeadAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			try {
//				final ISolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
//				return new ClearCoreDeadAnalysis(solver);
//			} catch (final ContradictionException e) {
//				return null;
//			}
//		} else {
//			return null;
//		}
//	}
//
//	private ClearImplicationAnalysis getAAAImplicationAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			try {
//				final ISolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
//				return new ClearImplicationAnalysis(solver);
//			} catch (final ContradictionException e) {
//				return null;
//			}
//		} else {
//			return null;
//		}
//	}
//
//	private Sat4JImplicationAnalysis getSat4JImplicationAnalysis(ISolverProblem problem) {
//		if (problem instanceof ISatProblem) {
//			try {
//				final Sat4JSatSolver solver = new Sat4JSatSolver((ISatProblem) problem, defaultConfiguration);
//				return new Sat4JImplicationAnalysis(solver);
//			} catch (final ContradictionException e) {
//				return null;
//			}
//		} else {
//			return null;
//		}
//	}

}
