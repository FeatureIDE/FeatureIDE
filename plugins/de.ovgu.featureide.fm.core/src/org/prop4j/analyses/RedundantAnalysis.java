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

import java.util.Arrays;

import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SatResult;
import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;
import org.sat4j.specs.IVecInt;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Computes redundant assumptions.
 *
 * @author Sebastian Krieter
 */
public class RedundantAnalysis extends AbstractAnalysis<int[]> {

	public RedundantAnalysis(ISatSolver solver) {
		super(solver);
	}

	public RedundantAnalysis(SatInstance satInstance) {
		super(satInstance);
	}

	@Override
	public int[] analyze(IMonitor monitor) {
		final IVecInt redundant = new VecInt();
		if (solver.isSatisfiable() == SatResult.TRUE) {
			final IVecInt assignment = solver.getAssignment();
			for (int i = 0; i < assignment.size(); i++) {
				final int literal = assignment.get(i);
				assignment.set(i, -literal);
				switch (solver.isSatisfiable()) {
				case FALSE:
					assignment.delete(i--);
					redundant.push(literal);
					break;
				case TIMEOUT:
				case TRUE:
					assignment.set(i, literal);
					break;
				}
			}
		}
		return Arrays.copyOf(redundant.toArray(), redundant.size());
	}

}
