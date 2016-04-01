/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.List;

import org.prop4j.solver.BasicSolver.SelectionStrategy;
import org.prop4j.solver.ISolverProvider;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Finds core and dead features.
 * 
 * @author Sebastian Krieter
 */
public class CoreDeadAnalysis extends SingleThreadAnalysis<List<String>> {

	public CoreDeadAnalysis(ISolverProvider solver) {
		super(solver);
	}

	public List<String> execute(WorkMonitor monitor) throws Exception {
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		int[] model1 = solver.findModel();
		solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
		int[] model2 = solver.findModel();

		if (model1 != null) {
			// if there are more negative than positive literals
			if (model1.length - countNegative(model1) < countNegative(model2)) {
				solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			}
			SatInstance.updateModel(model1, model2);
			for (int i = 0; i < model1.length; i++) {
				final int varX = model1[i];
				if (varX != 0) {
					solver.getAssignment().push(-varX);
					switch (solver.sat()) {
					case FALSE:
						solver.getAssignment().pop().unsafePush(varX);
						break;
					case TIMEOUT:
						solver.getAssignment().pop();
						break;
					case TRUE:
						solver.getAssignment().pop();
						SatInstance.updateModel(model1, solver.getModel());
						solver.shuffleOrder();
						break;
					}
				}
			}
		}

		return solver.getAssignmentString();
	}

	private static int countNegative(int[] model) {
		int count = 0;
		for (int i = 0; i < model.length; i++) {
			count += model[i] >>> (Integer.SIZE - 1);
		}
		return count;
	}

}
