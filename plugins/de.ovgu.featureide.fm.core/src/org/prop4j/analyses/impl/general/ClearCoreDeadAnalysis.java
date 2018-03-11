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

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class ClearCoreDeadAnalysis extends GeneralSolverAnalysis<int[]> {

	public ClearCoreDeadAnalysis(ISolver solver) {
		super(solver);
	}

	public ClearCoreDeadAnalysis(ISolver solver, int[] features) {
		super(solver);
		setFeatures(features);
	}

	private int[] features;

	@Override
	public int[] analyze(IMonitor monitor) {
		// Detect Core
		for (int i = 1; i <= solver.getProblem().getNumberOfVariables(); i++) {
			final int varX = i;
			try {
				solver.push(getLiteralFromIndex(-varX));
			} catch (final ContradictionException e1) {
				// If contradiction then it is unsatisfiable => core feature
				try {
					solver.push(getLiteralFromIndex(varX));
				} catch (final ContradictionException e) {}
				monitor.invoke(varX);
			}
			switch (solver.isSatisfiable()) {
			case FALSE:
				// If unsatisfiable => core feature
				solver.pop();
				try {
					solver.push(getLiteralFromIndex(varX));
				} catch (final ContradictionException e) {
					FMCorePlugin.getDefault().logError(e);
				}
				monitor.invoke(varX);
				break;
			case TIMEOUT:
				solver.pop();
				break;
			case TRUE:
				solver.pop();
				// solver.shuffleOrder();
				break;
			}

		}
		// Detect Dead
		for (int i = 1; i <= solver.getProblem().getNumberOfVariables(); i++) {
			final int varX = -i;
			try {
				solver.push(getLiteralFromIndex(-varX));
			} catch (final ContradictionException e1) {
				// If contradiction then it is unsatisfiable => dead feature
				try {
					solver.push(getLiteralFromIndex(varX));
				} catch (final ContradictionException e) {}
				monitor.invoke(varX);
			}
			switch (solver.isSatisfiable()) {
			case FALSE:
				// If unsatisfiable => dead feature
				solver.pop();
				try {
					solver.push(getLiteralFromIndex(varX));
				} catch (final ContradictionException e) {
					FMCorePlugin.getDefault().logError(e);
				}
				monitor.invoke(varX);
				break;
			case TIMEOUT:
				solver.pop();
				break;
			case TRUE:
				solver.pop();
				// solver.shuffleOrder();
				break;
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
