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

import org.prop4j.solver.BasicSolver;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.SatInstance;
import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds atomic sets.
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractAnalysis<T> implements LongRunningMethod<T> {

	protected ISatSolver solver;

	protected int[] assumptions = null;

	public AbstractAnalysis(SatInstance satInstance) {
		try {
			this.solver = new BasicSolver(satInstance);
		} catch (final ContradictionException e) {
			this.solver = null;
		}
	}

	public AbstractAnalysis(ISatSolver solver) {
		this.solver = solver;
	}

	@Override
	public final T execute(IMonitor monitor) throws Exception {
		if (solver == null) {
			return null;
		}
		if (assumptions != null) {
			for (final int assumption : assumptions) {
				solver.assignmentPush(assumption);
			}
		}
		monitor.checkCancel();
		try {
			return analyze(monitor);
		} catch (final Throwable e) {
			throw e;
		} finally {
			solver.assignmentClear(0);
		}
	}

	protected abstract T analyze(IMonitor monitor) throws Exception;

	public int[] getAssumptions() {
		return assumptions;
	}

	public void setAssumptions(int[] assumptions) {
		this.assumptions = assumptions;
	}

}
