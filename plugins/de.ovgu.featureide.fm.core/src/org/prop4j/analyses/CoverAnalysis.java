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

import java.util.ArrayList;
import java.util.List;

import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SatResult;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Computes a list of solutions that cover all given literals.
 *
 * @author Sebastian Krieter
 */
public class CoverAnalysis extends AbstractAnalysis<List<int[]>> {

	private final int[] literalsToCover;

	public CoverAnalysis(ISatSolver solver, int[] literalsToCover) {
		super(solver);
		this.literalsToCover = literalsToCover;
	}

	public CoverAnalysis(SatInstance satInstance, int[] literalsToCover) {
		super(satInstance);
		this.literalsToCover = literalsToCover;
	}

	@Override
	public List<int[]> analyze(IMonitor monitor) {
		final List<int[]> solutions = new ArrayList<>();
		if (solver.isSatisfiable() == SatResult.TRUE) {
			final int orgAssignmentSize = solver.getAssignment().size();
			int countCovered = 0;
			while (countCovered < literalsToCover.length) {
				final int countLastCovered = countCovered;
				for (int i = 0; i < literalsToCover.length; i++) {
					final int literal = literalsToCover[i];
					if (literal != 0) {
						solver.assignmentPush(literal);
						switch (solver.isSatisfiable()) {
						case FALSE:
							solver.assignmentReplaceLast(-literal);
							break;
						case TIMEOUT:
							solver.assignmentPop();
							break;
						case TRUE:
							literalsToCover[i] = 0;
							countCovered++;
							break;
						}
					}
				}
				if (countCovered == countLastCovered) {
					break;
				}
				solutions.add(solver.findModel());
				solver.assignmentClear(orgAssignmentSize);
			}
		}

		return solutions;
	}

}
