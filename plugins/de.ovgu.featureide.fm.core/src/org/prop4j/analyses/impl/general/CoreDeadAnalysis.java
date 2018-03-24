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
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.impl.SolverUtils;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class CoreDeadAnalysis extends GeneralSolverAnalysis<int[]> {

	public CoreDeadAnalysis(ISolver solver) {
		super(solver);
	}

	public CoreDeadAnalysis(ISolver solver, int[] features) {
		super(solver);
		setFeatures(features);
	}

	private int[] features;

	@Override
	public int[] analyze(IMonitor monitor) {
		solverSatisfiable();
		final int[] model1 = SolverUtils.getIntModel(solver.getSolution());
		for (int i = 0; i < model1.length; i++) {
			final int varX = model1[i];
			if (varX != 0) {
				try {
					solverPush(getLiteralFromIndex(-varX));
				} catch (final ContradictionException e) {
					// Unsatisfiable => dead or core feature
					try {
						solverPush(getLiteralFromIndex(varX));
					} catch (final ContradictionException e1) {
						// Should not be thrown
					}
					monitor.invoke(varX);
				}
				switch (solverSatisfiable()) {
				case FALSE:
					// Unsatisfiable => dead or core feature
					solverPop();
					try {
						solverPush(getLiteralFromIndex(varX));
					} catch (final ContradictionException e) {
						FMCorePlugin.getDefault().logError(e);
					}
					monitor.invoke(varX);
					break;
				case TIMEOUT:
					solverPop();
					break;
				case TRUE:
					solverPop();
					SolverUtils.updateModel(model1, SolverUtils.getIntModel(solver.getSolution()));
					break;
				}
			}
		}
		return getIntegerAssumptions();
	}

	public int[] getFeatures() {
		return features;
	}

	public void setFeatures(int[] features) {
		this.features = features;
	}
}
