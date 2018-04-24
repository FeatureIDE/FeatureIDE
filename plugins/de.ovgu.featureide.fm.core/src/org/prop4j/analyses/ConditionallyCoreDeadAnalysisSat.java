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
import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.configuration.Selection;
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
		super.analyze(monitor);
		monitor.setRemainingWork(solver.getSatInstance().getNumberOfVariables() + 2);

		final int[] knownValues = new int[solver.getSatInstance().getNumberOfVariables()];
		if (assumptions != null) {
			for (final int assumption : assumptions) {
				final int var = Math.abs(assumption);
				knownValues[var - 1] = assumption;
			}
			solver.getAssignment().ensure(assumptions.length + fixedVariables.length + 1);
		} else {
			solver.getAssignment().ensure(fixedVariables.length + 1);
		}

		for (int i = 0; i < fixedVariables.length; i++) {
			final int var = Math.abs(fixedVariables[i]);
			knownValues[var - 1] = fixedVariables[i];
		}
		solver.assignmentClear(0);
		for (final int var : knownValues) {
			if (var != 0) {
				solver.assignmentPush(var);
			}
		}

		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		final int[] unkownValues = solver.findModel();
		monitor.step();

		if (unkownValues != null) {
			for (int i = 0; i < knownValues.length; i++) {
				final int var = Math.abs(knownValues[i]);
				if (var != 0) {
					unkownValues[var - 1] = 0;
					monitor.step(new IntermediateResult(var, Selection.UNDEFINED));
				}
			}

			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			final int[] unkownValues2 = solver.findModel();
			monitor.step();

			// if there are more negative than positive literals
			solver.setSelectionStrategy((unkownValues.length < (countNegative(unkownValues2) + countNegative(unkownValues)) ? SelectionStrategy.POSITIVE
				: SelectionStrategy.NEGATIVE));

			updateModel(unkownValues, unkownValues2);

			VecInt varsToCompute = new VecInt(unkownValues.length);
			for (int i = 0; i < unkownValues.length; i++) {
				final int varX = unkownValues[i];
				if (varX != 0) {
					varsToCompute.push(Math.abs(varX));
				}
			}

			if (variableOrder != null) {
				final VecInt sortedVarsToCalulate = new VecInt(varsToCompute.size());
				for (int i = variableOrder.length - 1; i >= 0; i--) {
					final int var = variableOrder[i];
					if (varsToCompute.contains(var)) {
						sortedVarsToCalulate.push(var);
					}
				}
				varsToCompute = sortedVarsToCalulate;
			}

			while (!varsToCompute.isEmpty()) {
				final int var = varsToCompute.last();
				varsToCompute.pop();
				final int varX = unkownValues[var - 1];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					switch (solver.isSatisfiable()) {
					case FALSE:
						solver.assignmentReplaceLast(varX);
						monitor.step(new IntermediateResult(Math.abs(varX), varX < 0 ? Selection.UNSELECTED : Selection.SELECTED));
						break;
					case TIMEOUT:
						solver.assignmentPop();
						unkownValues[Math.abs(varX) - 1] = 0;
						monitor.step(new IntermediateResult(Math.abs(varX), Selection.UNDEFINED));
						break;
					case TRUE:
						solver.assignmentPop();
						updateModel(unkownValues, solver.getModel());
						solver.shuffleOrder();
						break;
					}
				}
			}
		}
		return solver.getAssignmentArray(0, solver.getAssignment().size());
	}

}
