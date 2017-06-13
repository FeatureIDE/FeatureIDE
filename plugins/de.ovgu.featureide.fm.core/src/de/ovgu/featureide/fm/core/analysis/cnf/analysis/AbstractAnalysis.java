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
package de.ovgu.featureide.fm.core.analysis.cnf.analysis;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Abstract analysis.
 * 
 * @author Sebastian Krieter
 */
public abstract class AbstractAnalysis<T> implements IAnalysis<T> {

	protected ISatSolver solver;

	protected LiteralSet assumptions = null;

	private T result;

	public AbstractAnalysis(CNF satInstance) {
		solver = initSolver(satInstance);
	}

	protected ISatSolver initSolver(CNF satInstance) {
		try {
			return new AdvancedSatSolver(satInstance);
		} catch (RuntimeContradictionException e) {
			return null;
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
			solver.assignmentPushAll(assumptions.getLiterals());
		}
		assumptions = new LiteralSet(solver.getAssignmentArray());

		monitor.checkCancel();
		try {
			result = analyze(monitor);
			return result;
		} catch (Throwable e) {
			throw e;
		} finally {
			solver.assignmentClear(0);
		}
	}

	protected abstract T analyze(IMonitor monitor) throws Exception;

	public LiteralSet getAssumptions() {
		return assumptions;
	}

	public void setAssumptions(LiteralSet assumptions) {
		this.assumptions = assumptions;
	}

	public AnalysisResult<T> getResult() {
		return new AnalysisResult<>(this.getClass().getName(), assumptions, result);
	}

}
