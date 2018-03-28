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

import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SatResult;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Tries to find a solution covering all given literals.
 *
 * @author Sebastian Krieter
 */
public class ResolveAnalysis extends AbstractAnalysis<int[]> {

	private final int[] literalsToResolve;

	public ResolveAnalysis(ISatSolver solver, int[] literalsToResolve) {
		super(solver);
		this.literalsToResolve = literalsToResolve;
	}

	public ResolveAnalysis(SatInstance satInstance, int[] literalsToResolve) {
		super(satInstance);
		this.literalsToResolve = literalsToResolve;
	}

	@Override
	public int[] analyze(IMonitor monitor) {
		final int orgAssignmentSize = solver.getAssignment().size();
		if (solver.isSatisfiable() == SatResult.TRUE) {
			for (int i = 0; i < literalsToResolve.length; i++) {
				final int literal = literalsToResolve[i];
				solver.assignmentPush(literal);
				switch (solver.isSatisfiable()) {
				case FALSE:
					solver.assignmentReplaceLast(-literal);
					break;
				case TIMEOUT:
					solver.assignmentPop();
					break;
				case TRUE:
					break;
				}
			}
		}
		return solver.getAssignmentArray(orgAssignmentSize, solver.getAssignment().size());
	}

}
