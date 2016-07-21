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

import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 * 
 * @author Sebastian Krieter
 */
public class ConditionallyCoreDeadAnalysis extends AbstractAnalysis<int[]> {

	protected int[] fixedVariables;
	protected int newCount;

	public ConditionallyCoreDeadAnalysis(ISatSolver solver) {
		super(solver);
		resetFixedFeatures();
	}

	public ConditionallyCoreDeadAnalysis(SatInstance satInstance) {
		super(satInstance);
		resetFixedFeatures();
	}

	public void setFixedFeatures(int[] fixedVariables, int newCount) {
		this.fixedVariables = fixedVariables;
		this.newCount = newCount;
	}

	public void resetFixedFeatures() {
		fixedVariables = new int[0];
		newCount = 0;
	}

	public int[] analyze(IMonitor monitor) throws Exception {
		for (int i = 0; i < fixedVariables.length; i++) {
			solver.getAssignment().push(fixedVariables[i]);
		}
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		int[] model1 = solver.findModel();
		solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
		int[] model2 = solver.findModel();

		monitor.checkCancel();

		if (model1 != null) {
			// if there are more negative than positive literals
			if (model1.length - countNegative(model1) < countNegative(model2)) {
				solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			}
			for (int i = 0; i < fixedVariables.length; i++) {
				 model1[Math.abs(fixedVariables[i]) - 1] = 0;
			}
			SatInstance.updateModel(model1, model2);
			for (int i = 0; i < model1.length; i++) {
				monitor.checkCancel();
				final int varX = model1[i];
				if (varX != 0) {
					solver.getAssignment().push(-varX);
					switch (solver.isSatisfiable()) {
					case FALSE:
						solver.getAssignment().pop().unsafePush(varX);
						monitor.invoke(solver.getSatInstance().getVariableObject(varX));
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
		int[] result = new int[solver.getAssignment().size()];
		solver.getAssignment().copyTo(result);
		return result;
	}

	protected static int countNegative(int[] model) {
		int count = 0;
		for (int i = 0; i < model.length; i++) {
			count += model[i] >>> (Integer.SIZE - 1);
		}
		return count;
	}

}
