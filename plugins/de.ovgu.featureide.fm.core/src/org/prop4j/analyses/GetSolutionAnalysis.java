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
import java.util.Collections;
import java.util.List;

import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Computes valid solutions for the given {@link SatInstance}.
 *
 * @author Sebastian Krieter
 */
public class GetSolutionAnalysis extends AbstractAnalysis<List<int[]>> {

	private int maxSolutions;
	private boolean uniqueSolutions;

	public GetSolutionAnalysis(SatInstance satInstance) {
		this(satInstance, Integer.MAX_VALUE, true);
	}

	public GetSolutionAnalysis(SatInstance satInstance, int maxSolutions, boolean uniqueSolutions) {
		super(satInstance);
		this.maxSolutions = maxSolutions;
		this.uniqueSolutions = uniqueSolutions;
	}

	@Override
	public List<int[]> analyze(IMonitor monitor) throws Exception {
		final List<int[]> solutions = new ArrayList<>();
		solutionLoop: for (int i = 0; i < maxSolutions; i++) {
			switch (solver.isSatisfiable()) {
			case TIMEOUT:
				return Collections.emptyList();
			case FALSE:
				break solutionLoop;
			case TRUE:
				final int[] model = solver.getModel();
				solutions.add(model);
				if (uniqueSolutions) {
					try {
						solver.getInternalSolver().addClause(new VecInt(SatInstance.negateModel(model)));
					} catch (final ContradictionException e) {
						break solutionLoop;
					}
				}
				solver.shuffleOrder();
				break;
			default:
				throw new RuntimeException();
			}
		}
		return solutions;
	}

	public int getMaxSolutions() {
		return maxSolutions;
	}

	public void setMaxSolutions(int maxSolutions) {
		this.maxSolutions = maxSolutions;
	}

	public boolean isUniqueSolutions() {
		return uniqueSolutions;
	}

	public void setUniqueSolutions(boolean uniqueSolutions) {
		this.uniqueSolutions = uniqueSolutions;
	}

}
