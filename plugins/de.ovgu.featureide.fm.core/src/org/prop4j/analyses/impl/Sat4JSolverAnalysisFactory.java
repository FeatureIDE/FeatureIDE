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
import org.prop4j.analyses.impl.cleanGeneral.AAACoreDeadAnalysis;
import org.prop4j.analyses.impl.cleanGeneral.AAAImplicationAnalysis;
import org.prop4j.analyses.impl.general.ConstraintsUnsatisfiableAnaylsis;
import org.prop4j.analyses.impl.general.CoreDeadAnalysis;
import org.prop4j.analyses.impl.general.ImplicationAnalysis;
import org.prop4j.analyses.impl.general.IndeterminedAnalysis;
import org.prop4j.analyses.impl.general.RedundantConstraintAnalysis;
import org.prop4j.analyses.impl.general.ValidAnalysis;
import org.prop4j.analyses.impl.sat4j.Sat4JCoreDeadAnalysis;
import org.prop4j.analyses.impl.sat4j.Sat4JImplicationAnalysis;
import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.ISolverProblem;
import org.prop4j.solver.impl.sat4j.Sat4jSatSolver;

/**
 * Default factory used to create analysis with their appropriate solver.
 *
 * @author Joshua Sprey
 */
public class Sat4JSolverAnalysisFactory extends AbstractSolverAnalysisFactory {

	private final HashMap<String, Object> defaultConfiguration = new HashMap<String, Object>();

	/**
	 *
	 */
	public Sat4JSolverAnalysisFactory() {
		defaultConfiguration.put(AbstractSatSolver.CONFIG_TIMEOUT, 1000);
		defaultConfiguration.put(AbstractSatSolver.CONFIG_DB_SIMPLIFICATION_ALLOWED, true);
		defaultConfiguration.put(AbstractSatSolver.CONFIG_VERBOSE, false);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.ISolverAnalysisFactory#getAnalysis(java.lang.Object, org.prop4j.solver.ISolverProblem)
	 */
	@Override
	public ISolverAnalysis<?> getAnalysis(Class<?> analysisClass, ISolverProblem problem) {
		if (analysisClass.equals(ValidAnalysis.class)) {
			return getValidAnalyis(problem);
		} else if (analysisClass.equals(CoreDeadAnalysis.class)) {
			return getCoreDeadAnalysis(problem);
		} else if (analysisClass.equals(ImplicationAnalysis.class)) {
			return getImplicationAnalysis(problem);
		} else if (analysisClass.equals(IndeterminedAnalysis.class)) {
			return getIndeterminedAnalysis(problem);
		} else if (analysisClass.equals(RedundantConstraintAnalysis.class)) {
			return getRedundantConstraintAnalysis(problem);
		} else if (analysisClass.equals(ConstraintsUnsatisfiableAnaylsis.class)) {
			return getConstraintsUnsatisfiableAnaylsis(problem);// Start AAAAAAAAAAAAAAAAAAAAAAS
		}

		// Check for AAA analysis
		if (analysisClass.equals(AAACoreDeadAnalysis.class)) {
			return getAAACoreDeadAnalysis(problem);
		} else if (analysisClass.equals(AAAImplicationAnalysis.class)) {
			return getAAAImplicationAnalysis(problem);
		}

		// Check for SAT4J analysis
		if (analysisClass.equals(Sat4JCoreDeadAnalysis.class)) {
			return getSat4JCoreDeadAnalysis(problem);
		} else if (analysisClass.equals(Sat4JImplicationAnalysis.class)) {
			return getSat4JImplicationAnalysis(problem);
		}
		return null;
	}

	private CoreDeadAnalysis getCoreDeadAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new CoreDeadAnalysis(solver);
		} else {
			return null;
		}
	}

	private ValidAnalysis getValidAnalyis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new ValidAnalysis(solver);
		} else {
			return null;
		}
	}

	private ImplicationAnalysis getImplicationAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new ImplicationAnalysis(solver);
		} else {
			return null;
		}
	}

	private IndeterminedAnalysis getIndeterminedAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new IndeterminedAnalysis(solver, null);
		} else {
			return null;
		}
	}

	private RedundantConstraintAnalysis getRedundantConstraintAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new RedundantConstraintAnalysis(solver, this);
		} else {
			return null;
		}
	}

	private ConstraintsUnsatisfiableAnaylsis getConstraintsUnsatisfiableAnaylsis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new ConstraintsUnsatisfiableAnaylsis(solver, this);
		} else {
			return null;
		}
	}

	private AAACoreDeadAnalysis getAAACoreDeadAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new AAACoreDeadAnalysis(solver);
		} else {
			return null;
		}
	}

	private AAAImplicationAnalysis getAAAImplicationAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new AAAImplicationAnalysis(solver);
		} else {
			return null;
		}
	}

	private Sat4JImplicationAnalysis getSat4JImplicationAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final Sat4jSatSolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new Sat4JImplicationAnalysis(solver);
		} else {
			return null;
		}
	}

	private Sat4JCoreDeadAnalysis getSat4JCoreDeadAnalysis(ISolverProblem problem) {
		if (problem instanceof ISatProblem) {
			final Sat4jSatSolver solver = new Sat4jSatSolver((ISatProblem) problem, defaultConfiguration);
			return new Sat4JCoreDeadAnalysis(solver);
		} else {
			return null;
		}
	}

}
