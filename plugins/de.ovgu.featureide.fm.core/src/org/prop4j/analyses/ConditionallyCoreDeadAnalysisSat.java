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
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 */
public class ConditionallyCoreDeadAnalysisSat extends AConditionallyCoreDeadAnalysis {

	public ConditionallyCoreDeadAnalysisSat(ISatSolver solver) {
		super(solver);
	}

	public ConditionallyCoreDeadAnalysisSat(SatInstance satInstance) {
		super(satInstance);
	}

	@Override
	public int[] analyze(IMonitor monitor) throws Exception {
		satCount = 0;
		solver.getAssignment().ensure(fixedVariables.length);
		for (int i = 0; i < fixedVariables.length; i++) {
			solver.assignmentPush(fixedVariables[i]);
		}
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		final int[] model1 = solver.findModel();
		satCount++;

		if (model1 != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			final int[] model2 = solver.findModel();
			satCount++;

			// if there are more negative than positive literals
			solver.setSelectionStrategy(
					(model1.length < (countNegative(model2) + countNegative(model1)) ? SelectionStrategy.POSITIVE : SelectionStrategy.NEGATIVE));

			for (int i = 0; i < fixedVariables.length; i++) {
				model1[Math.abs(fixedVariables[i]) - 1] = 0;
			}

			SatInstance.updateModel(model1, model2);
			for (int i = 0; i < model1.length; i++) {
				final int varX = model1[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					satCount++;
					switch (solver.isSatisfiable()) {
					case FALSE:
						solver.assignmentReplaceLast(varX);
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.assignmentPop();
						SatInstance.updateModel(model1, solver.getModel());
						solver.shuffleOrder();
						break;
					}
				}
			}
		}
		return solver.getAssignmentArray(0, solver.getAssignment().size());
	}

	@Override
	public String toString() {
		return "SAT_Improved";
	}

}
