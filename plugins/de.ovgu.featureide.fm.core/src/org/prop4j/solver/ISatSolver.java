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

/**
 * Interface to identify the current solver as an sat solver.
 *
 * @author Joshua Sprey
 */
public interface ISatSolver extends ISolver {

	public static final String CONFIG_TIMEOUT = "Timeout";
	public static final String CONFIG_VERBOSE = "Verbose";
	public static final String CONFIG_DB_SIMPLIFICATION_ALLOWED = "DBSimplification";
	public static final String CONFIG_SELECTION_STRATEGY = "SelectionStrategy";

	public static final int MAX_SOLUTION_BUFFER = 1000;

	public static enum SelectionStrategy {
		NEGATIVE, ORG, POSITIVE, RANDOM, UNIFORM_RANDOM, FIXED
	}
}
