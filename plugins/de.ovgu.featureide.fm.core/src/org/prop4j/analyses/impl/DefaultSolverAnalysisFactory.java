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
import org.prop4j.analyses.impl.general.CoreDeadAnalysis;
import org.prop4j.analyses.impl.general.ValidAnalysis;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.ISolverProblem;
import org.prop4j.solver.impl.sat4j.Sat4jSatSolver;

/**
 * Default factory used to create analysis with their appropriate solver.
 *
 * @author Joshua Sprey
 */
public class DefaultSolverAnalysisFactory extends AbstractSolverAnalysisFactory {

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.ISolverAnalysisFactory#getAnalysis(java.lang.Object, org.prop4j.solver.ISolverProblem)
	 */
	@Override
	public ISolverAnalysis<?> getAnalysis(Class<?> analysisClass, ISolverProblem problem) {
		if (analysisClass.equals(ValidAnalysis.class)) {
			final HashMap<String, Object> configuration = new HashMap<>();
			configuration.put(Sat4jSatSolver.CONFIG_TIMEOUT, 1000);
			configuration.put(Sat4jSatSolver.CONFIG_DB_SIMPLIFICATION_ALLOWED, true);
			configuration.put(Sat4jSatSolver.CONFIG_VERBOSE, true);
			if (problem instanceof ISatProblem) {
				final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, configuration);
				return new ValidAnalysis(solver);
			}
		} else if (analysisClass.equals(CoreDeadAnalysis.class)) {
			final HashMap<String, Object> configuration = new HashMap<>();
			configuration.put(Sat4jSatSolver.CONFIG_TIMEOUT, 1000);
			configuration.put(Sat4jSatSolver.CONFIG_DB_SIMPLIFICATION_ALLOWED, true);
			configuration.put(Sat4jSatSolver.CONFIG_VERBOSE, true);
			if (problem instanceof ISatProblem) {
				final ISolver solver = new Sat4jSatSolver((ISatProblem) problem, configuration);
				return new CoreDeadAnalysis(solver);
			}
		}
		return null;
	}
}
