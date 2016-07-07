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

import org.prop4j.solver.BasicSolver;
import org.prop4j.solver.SatInstance;
import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Finds atomic sets.
 * 
 * @author Sebastian Krieter
 */
public abstract class SingleThreadAnalysis<T> implements LongRunningMethod<T> {

	protected static final int MAX_SOLUTION_BUFFER = 1000;

	protected BasicSolver solver;

	protected int[] assumptions = null;

	public SingleThreadAnalysis(SatInstance satInstance) {
		try {
			this.solver = new BasicSolver(satInstance);
		} catch (ContradictionException e) {
			this.solver = null;
		}
	}

	public SingleThreadAnalysis(BasicSolver solver) {
		this.solver = solver;
	}

	@Override
	public final T execute(WorkMonitor monitor) throws Exception {
		if (solver == null) {
			return null;
		}
		if (assumptions != null) {
			for (int assumption : assumptions) {
				solver.getAssignment().push(assumption);
			}
		}
		monitor.checkCancel();
		try {
			return analyze(monitor);
		} catch (Throwable e) {
			throw e;
		} finally {
			solver.getAssignment().clear();
		}
	}

	protected abstract T analyze(WorkMonitor monitor) throws Exception;

	public int[] getAssumptions() {
		return assumptions;
	}

	public void setAssumptions(int[] assumptions) {
		this.assumptions = assumptions;
	}

}
