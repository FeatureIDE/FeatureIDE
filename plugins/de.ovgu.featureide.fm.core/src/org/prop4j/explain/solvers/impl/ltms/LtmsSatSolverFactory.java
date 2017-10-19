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
package org.prop4j.explain.solvers.impl.ltms;

import org.prop4j.explain.solvers.MusExtractor;
import org.prop4j.explain.solvers.MutableSatSolver;
import org.prop4j.explain.solvers.SatSolver;
import org.prop4j.explain.solvers.SatSolverFactory;

/**
 * Provides instances of {@link SatSolver} using an {@link Ltms LTMS}.
 *
 * @author Timo G&uuml;nther
 */
public class LtmsSatSolverFactory extends SatSolverFactory {

	@Override
	public SatSolver getSatSolver() {
		return new Ltms();
	}

	@Override
	public MutableSatSolver getMutableSatSolver() {
		return new Ltms();
	}

	@Override
	public MusExtractor getMusExtractor() {
		return new Ltms();
	}
}
