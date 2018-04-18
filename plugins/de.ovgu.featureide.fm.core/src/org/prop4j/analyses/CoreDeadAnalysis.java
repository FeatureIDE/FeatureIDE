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

import org.prop4j.solver.FixedLiteralSelectionStrategy;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;
import org.prop4j.solver.VarOrderHeap2;
import org.sat4j.minisat.core.Solver;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 */
public class CoreDeadAnalysis extends AbstractAnalysis<int[]> {

	public CoreDeadAnalysis(ISatSolver solver) {
		this(solver, null);
	}

	private int[] features;

	public CoreDeadAnalysis(SatInstance satInstance) {
		this(satInstance, null);
	}

	public CoreDeadAnalysis(SatInstance satInstance, int[] features) {
		super(satInstance);
		setFeatures(features);
	}

	public CoreDeadAnalysis(ISatSolver solver, int[] features) {
		super(solver);
		setFeatures(features);
	}

	@Override
	public int[] analyze(IMonitor monitor) throws Exception {
		final int orgAssignmentSize = solver.getAssignment().size();
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		int[] model1 = solver.findModel();

		if (model1 != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			final int[] model2 = solver.findModel();

			if (features != null) {
				final int[] model3 = new int[model1.length];
				for (int i = 0; i < features.length; i++) {
					final int index = features[i] - 1;
					if (index >= 0) {
						model3[index] = model1[index];
					}
				}
				model1 = model3;
			}

			SatInstance.updateModel(model1, model2);
			((Solver<?>) solver.getInternalSolver()).setOrder(new VarOrderHeap2(new FixedLiteralSelectionStrategy(model1, true), solver.getOrder()));

			for (int i = 0; i < model1.length; i++) {
				final int varX = model1[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					switch (solver.isSatisfiable()) {
					case FALSE:
						solver.assignmentReplaceLast(varX);
						monitor.invoke(varX);
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

		return solver.getAssignmentArray(orgAssignmentSize, solver.getAssignment().size());
	}

	public int[] getFeatures() {
		return features;
	}

	public void setFeatures(int[] features) {
		this.features = features;
	}

}
