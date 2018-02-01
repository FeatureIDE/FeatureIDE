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

import org.prop4j.solver.ISolver;

import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Represents an analysis that can be solved either by SMT or SAT solvers.
 *
 * @author Joshua Sprey
 */
public abstract class GeneralSolverAnalysis<T> implements ISolverAnalysis<T>, LongRunningMethod<T> {

	protected ISolver solver;

	protected GeneralSolverAnalysis(ISolver solver) {
		this.solver = solver;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.job.LongRunningMethod#execute(de.ovgu.featureide.fm.core.job.monitor.IMonitor)
	 */
	@Override
	public final T execute(IMonitor monitor) throws Exception {
		if (solver == null) {
			return null;
		}
//		if (assumptions != null) {
//			for (final int assumption : assumptions) {
//				solver.assignmentPush(assumption);
//			}
//		}
		monitor.checkCancel();
		try {
			return analyze(monitor);
		} catch (final Throwable e) {
			throw e;
		} finally {
//			solver.assignmentClear(0);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.ISolverAnalysis#analyze(de.ovgu.featureide.fm.core.job.monitor.IMonitor)
	 */
	@Override
	public T analyze(IMonitor monitor) {
		// TODO Auto-generated method stub
		return null;
	}

}
