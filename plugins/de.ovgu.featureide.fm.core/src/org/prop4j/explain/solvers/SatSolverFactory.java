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
package org.prop4j.explain.solvers;

import org.prop4j.explain.solvers.impl.sat4j.Sat4jSatSolverFactory;

/**
 * Provides instances of {@link SatSolver}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class SatSolverFactory {

	/**
	 * Returns a default instance of this class.
	 *
	 * @return a default instance of this class
	 */
	public static SatSolverFactory getDefault() {
		return new Sat4jSatSolverFactory();
	}

	/**
	 * Returns an instance of {@link SatSolver}.
	 *
	 * @return an instance of {@link SatSolver}
	 */
	public abstract SatSolver getSatSolver();

	/**
	 * Returns an instance of {@link MutableSatSolver}.
	 *
	 * @return an instance of {@link MutableSatSolver}
	 */
	public abstract MutableSatSolver getMutableSatSolver();

	/**
	 * Returns an instance of {@link MusExtractor}.
	 *
	 * @return an instance of {@link MusExtractor}
	 */
	public abstract MusExtractor getMusExtractor();
}
