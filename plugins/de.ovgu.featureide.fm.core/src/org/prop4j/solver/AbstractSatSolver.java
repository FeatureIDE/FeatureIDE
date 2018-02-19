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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

/**
 * Abstract class for the sat solvers.
 *
 * @author Joshua Sprey
 */
public abstract class AbstractSatSolver implements ISatSolver {

	ISatProblem problem;

	public static final String CONFIG_TIMEOUT = "Timeout";
	public static final String CONFIG_VERBOSE = "Verbose";
	public static final String CONFIG_DB_SIMPLIFICATION_ALLOWED = "DBSimplification";
	public static final String CONFIG_SELECTION_STRATEGY = "SelectionStrategy";

	/**
	 * Create a new Sat solver.
	 *
	 * @param problem The problem that the solver should solve.
	 */
	public AbstractSatSolver(ISatProblem problem) {
		this.problem = problem;
	}

	/**
	 * Create a new Sat solver.
	 *
	 * @param problem The problem that the solver should solve.
	 * @param config The configurations for the solver.
	 */
	public AbstractSatSolver(ISatProblem problem, Map<String, Object> config) {
		this.problem = problem;
		setConfiguration(config);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getProblem()
	 */
	@Override
	public ISolverProblem getProblem() {
		return problem;
	}

	@Override
	public List<String> setConfiguration(Map<String, Object> config) {
		if (config == null) {
			return null;
		}
		final HashSet<String> list = new HashSet<>();
		for (final String configID : config.keySet()) {
			final Object value = config.get(configID);
			if (setConfiguration(configID, value)) {
				list.add(configID);
			}
		}
		return new ArrayList<>(list);
	}

}
