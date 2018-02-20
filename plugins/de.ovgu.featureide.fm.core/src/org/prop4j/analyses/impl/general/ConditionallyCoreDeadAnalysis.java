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
package org.prop4j.analyses.impl.general;

import org.prop4j.analyses.GeneralSolverAnalysis;
import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.AbstractSatSolver.SatSolverSelectionStrategy;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.impl.SolverUtils;
import org.prop4j.solverOld.SatInstance;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 */
public class ConditionallyCoreDeadAnalysis extends GeneralSolverAnalysis<int[]> {

	public ConditionallyCoreDeadAnalysis(ISolver solver) {
		super(solver);
	}

	@Override
	public int[] analyze(IMonitor monitor) {
		solver.setConfiguration(AbstractSatSolver.CONFIG_SELECTION_STRATEGY, SatSolverSelectionStrategy.POSITIVE);
		final int[] model1 = SolverUtils.getIntModel(solver.findSolution());

		if (model1 != null) {
			solver.setConfiguration(AbstractSatSolver.CONFIG_SELECTION_STRATEGY, SatSolverSelectionStrategy.NEGATIVE);
			final int[] model2 = SolverUtils.getIntModel(solver.findSolution());

			SatInstance.updateModel(model1, model2);
//			for (int i = 0; i < assumptions.length; i++) {
//				model1[Math.abs(assumptions[i]) - 1] = 0;
//			}

//			((Solver<?>) solver.getInternalSolver()).setOrder(new VarOrderHeap2(new FixedLiteralSelectionStrategy(model1, true), solver.getOrder()));
			try {

				for (int i = 0; i < model1.length; i++) {
					final int varX = model1[i];
					if (varX != 0) {
						solver.push(getLiteralFromIndex(-varX));
						switch (solver.isSatisfiable()) {
						case FALSE:
							solver.pop();
							solver.push(getLiteralFromIndex(varX));
							break;
						case TIMEOUT:
							solver.pop();
							break;
						case TRUE:
							solver.pop();
							SatInstance.updateModel(model1, SolverUtils.getIntModel(solver.findSolution()));
//							solver.shuffleOrder();
							break;
						}
					}
				}
			} catch (final ContradictionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		return getIntegerAssumptions();
	}

}
