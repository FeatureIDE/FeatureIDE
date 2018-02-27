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
package org.prop4j.analyses.impl.sat4j;

import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.impl.SolverUtils;
import org.prop4j.solver.impl.sat4j.Sat4jSatSolver;
import org.prop4j.solverOld.FixedLiteralSelectionStrategy;
import org.prop4j.solverOld.SatInstance;
import org.prop4j.solverOld.VarOrderHeap2;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features. Especially optimized for the Sat4J Sat solver.
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class Sat4JCoreDeadAnalysis extends AbstractSat4JAnalysis<int[]> {

	public Sat4JCoreDeadAnalysis(Sat4jSatSolver solver) {
		super(solver);
	}

	private int[] features;

	public void setFeatures(int[] features) {
		this.features = features;
	}

	@Override
	public int[] analyze(IMonitor monitor) {
		if (!(getSolver() instanceof Sat4jSatSolver)) {
			return null;
		}

		solver.setConfiguration(AbstractSatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.POSITIVE);
		int[] model1 = SolverUtils.getIntModel(solver.findSolution());

		if (model1 != null) {
			solver.setConfiguration(AbstractSatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.NEGATIVE);
			final int[] model2 = SolverUtils.getIntModel(solver.findSolution());
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

			SolverUtils.updateModel(model1, model2);
			solver.getInternalSolver().setOrder(new VarOrderHeap2(new FixedLiteralSelectionStrategy(model1, true), solver.getOrder()));

			for (int i = 0; i < model1.length; i++) {
				final int varX = model1[i];
				if (varX != 0) {
					try {
						solver.push(getLiteralFromIndex(-varX));
					} catch (final ContradictionException e) {
						solver.pop();
						try {
							solver.push(getLiteralFromIndex(varX));
						} catch (final ContradictionException e1) {
							// Should not happen
						}
						monitor.invoke(varX);
					}
					switch (solver.isSatisfiable()) {
					case FALSE:
						solver.pop();
						try {
							solver.push(getLiteralFromIndex(varX));
						} catch (final ContradictionException e) {
							// Should not happen
						}
						monitor.invoke(varX);
						break;
					case TIMEOUT:
						solver.pop();
						break;
					case TRUE:
						solver.pop();
						SatInstance.updateModel(model1, SolverUtils.getIntModel(solver.findSolution()));
						solver.pop();
						break;
					}
				}
			}
		}

		return getIntegerAssumptions();
	}

}
