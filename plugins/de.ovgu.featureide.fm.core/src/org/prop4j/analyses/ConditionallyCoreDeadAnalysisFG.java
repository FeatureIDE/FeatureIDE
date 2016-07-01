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
package org.prop4j.analyses;

import org.prop4j.solver.BasicSolver.SelectionStrategy;
import org.prop4j.solver.ISolverProvider;
import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.conf.AFeatureGraph;
import de.ovgu.featureide.fm.core.conf.IFeatureGraph;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Finds core and dead features.
 * 
 * @author Sebastian Krieter
 */
public class ConditionallyCoreDeadAnalysisFG extends ConditionallyCoreDeadAnalysis {

	private final IFeatureGraph featureGraph;

	public ConditionallyCoreDeadAnalysisFG(ISolverProvider solver, IFeatureGraph featureGraph) {
		super(solver);
		this.featureGraph = featureGraph;
	}

	public int[] execute(WorkMonitor monitor) throws Exception {
		solver.getAssignment().clear();

		solver.getAssignment().ensure(fixedVariables.length);
		for (int i = 0; i < fixedVariables.length; i++) {
			final int var = fixedVariables[i];
			solver.getAssignment().push(var);
		}
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		final int[] model1 = solver.findModel();
		solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
		final int[] model2 = solver.findModel();

		monitor.checkCancel();

		if (model1 != null) {
			// monitor.setMaxAbsoluteWork(model1.length);

			// if there are more negative than positive literals
			solver.setSelectionStrategy((model1.length < countNegative(model2) + countNegative(model1) 
				? SelectionStrategy.POSITIVE 
				: SelectionStrategy.NEGATIVE));
			
			SatInstance.updateModel(model1, model2);
			for (int i = 0; i < fixedVariables.length; i++) {
				model1[Math.abs(fixedVariables[i]) - 1] = 0;
			}

			final VecInt v = new VecInt();
			for (int i = 0; i < newCount; i++) {
				int var = fixedVariables[i];
				traverse(model1, v, var);
			}

			sat(model1, v);
		}
		int[] result = new int[solver.getAssignment().size()];
		solver.getAssignment().copyTo(result);
		return result;
	}

	private void sat(int[] model1, VecInt v) {
		while (!v.isEmpty()) {
			final int varX = v.get(v.size() - 1);
			v.pop();
			if (model1[Math.abs(varX) - 1] == varX) {
				solver.getAssignment().push(-varX);
				switch (solver.sat()) {
				case FALSE:
					solver.getAssignment().pop().unsafePush(varX);
					traverse2(v, varX);
					break;
				case TIMEOUT:
					throw new RuntimeException();
				case TRUE:
					solver.getAssignment().pop();
					SatInstance.updateModel(model1, solver.getModel());
					solver.shuffleOrder();
					break;
				}
			}
		}
	}

	private void traverse(int[] model1, VecInt v, int var) {
		final boolean fromSelected = var > 0;

		for (int j = 0; j < model1.length; j++) {
			if (model1[j] != 0) {
				final byte value = featureGraph.getValueInternal(Math.abs(var) - 1, j, fromSelected);
				switch (value) {
				case AFeatureGraph.VALUE_0:
					solver.getAssignment().push(-(j + 1));
					break;
				case AFeatureGraph.VALUE_1:
					solver.getAssignment().push((j + 1));
					break;
				case AFeatureGraph.VALUE_0Q:
					v.push(-(j + 1));
					break;
				case AFeatureGraph.VALUE_1Q:
					v.push(j + 1);
					break;
				case AFeatureGraph.VALUE_10Q:
					v.push(-(j + 1));
					v.push(j + 1);
					break;
				default:
					break;
				}
			}
		}
	}

	private void traverse2(VecInt v, int var) {
		final boolean fromSelected = var > 0;

		for (int i = v.size() - 1; i >= 0; i--) {
			final int varX = v.get(i);
			final byte value = featureGraph.getValueInternal(Math.abs(var) - 1, Math.abs(varX) - 1, fromSelected);
			switch (value) {
			case AFeatureGraph.VALUE_0:
				if (varX < 0) {
					solver.getAssignment().push(varX);
				}
				v.delete(i);
				break;
			case AFeatureGraph.VALUE_1:
				if (varX > 0) {
					solver.getAssignment().push(varX);
				}
				v.delete(i);
				break;
			default:
				break;
			}
		}
	}

}
