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
package org.prop4j.analyses;

import org.prop4j.analyses.impl.DefaultSolverAnalysisFactory;
import org.prop4j.solver.ISolverProblem;

/**
 * Interface used to create all analysis and their used Solvers. Needs to be implemented for concrete factory's to create the analysis with appropriate solver.
 *
 * @author Joshua Sprey
 */
public abstract class AbstractSolverAnalysisFactory {

	/**
	 * Returns the default factory used. See {@link DefaultSolverAnalysisFactory}
	 *
	 * @return Default factory.
	 */
	public static AbstractSolverAnalysisFactory getDefault() {
		return new DefaultSolverAnalysisFactory();
	}

	/**
	 * Creates an anylsis for a given class. Also determine especially which solver is used to solve the analysis.
	 *
	 * @param analysisClass Class of the analysis as Object.
	 * @param problem Problem which should be looked at at the analysis.
	 * @return New instance of the given analysis class that use the given solver.
	 */
	public abstract ISolverAnalysis<?> getAnalysis(Class<?> analysisClass, ISolverProblem problem);
}
