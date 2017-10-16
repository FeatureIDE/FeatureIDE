/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf.analysis;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Determines whether a sat instance is satisfiable and returns the found model.
 *
 * @author Sebastian Krieter
 */
public class HasSolutionAnalysis extends AbstractAnalysis<Boolean> {

	public HasSolutionAnalysis(ISatSolver solver) {
		super(solver);
	}

	public HasSolutionAnalysis(CNF satInstance) {
		super(satInstance);
	}

	@Override
	public Boolean analyze(IMonitor monitor) throws Exception {
		final SatResult hasSolution = solver.hasSolution();
		switch (hasSolution) {
		case FALSE:
			return false;
		case TIMEOUT:
			reportTimeout();
			return false;
		case TRUE:
			return true;
		default:
			throw new AssertionError(hasSolution);
		}
	}

}
