/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Random;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeTimeoutException;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Abstract analysis.
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractAnalysis<T> implements IAnalysis<T> {

	protected ISatSolver solver;

	protected Random random = new Random(112358);

	protected LiteralSet assumptions = null;

	private boolean timeoutOccured = false;
	private boolean throwTimeoutException = true;

	private T result = null;

	public AbstractAnalysis(CNF satInstance) {
		solver = initSolver(satInstance);
	}

	protected ISatSolver initSolver(CNF satInstance) {
		try {
			return new AdvancedSatSolver(satInstance);
		} catch (final RuntimeContradictionException e) {
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
		timeoutOccured = false;

		monitor.checkCancel();
		try {
			result = analyze(monitor);
			return result;
		} catch (final Throwable e) {
			throw e;
		} finally {
			solver.assignmentClear(0);
		}
	}

	protected abstract T analyze(IMonitor monitor) throws Exception;

	protected final void reportTimeout() throws RuntimeTimeoutException {
		timeoutOccured = true;
		if (throwTimeoutException) {
			throw new RuntimeTimeoutException();
		}
	}

	@Override
	public final LiteralSet getAssumptions() {
		return assumptions;
	}

	@Override
	public final void setAssumptions(LiteralSet assumptions) {
		this.assumptions = assumptions;
	}

	public final boolean isThrowTimeoutException() {
		return throwTimeoutException;
	}

	public final void setThrowTimeoutException(boolean throwTimeoutException) {
		this.throwTimeoutException = throwTimeoutException;
	}

	public final boolean isTimeoutOccured() {
		return timeoutOccured;
	}

	@Override
	public final AnalysisResult<T> getResult() {
		return new AnalysisResult<>(this.getClass().getName(), assumptions, result);
	}

	public Random getRandom() {
		return random;
	}

	public void setRandom(Random random) {
		this.random = random;
	}

}
