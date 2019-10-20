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

import java.util.Random;

import org.prop4j.solver.ISolver;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AnalysisResult;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.RuntimeTimeoutException;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Represents an analysis that can be solved either by SMT or SAT solvers.
 *
 * @author Joshua Sprey
 */
public abstract class GeneralSolverAnalysis<T> implements ISolverAnalysis<T> {

	/** The list containing all assumption that are added to the solver before the analysis. */
	protected LiteralSet assumptions = null;

	/** Random object used to randomize the execution of the analysis. */
	protected Random random = new Random(112358);

	/** The result for the analysis. */
	private T result = null;

	/** Indicate that a timeout exception should be thrown when the timeout was exceeded. */
	private boolean throwTimeoutException = true;
	/** The time in ms before the solver timeouts. */
	private int timeout = 10_000;

	/** Indicate that a timeout occurred. */
	private boolean timeoutOccured = false;

	/**
	 * This method executes the analysis that should be realized. The monitor should be used at the appropriate placed for {@link IMonitor#checkCancel()} to
	 * interrupt an analysis effectively.
	 *
	 * @param monitor Monitor to monitor the analysis. Shoudl be used for cancel checks.
	 * @return The results of the analysis. The result can also be retrieved via {@link GeneralSolverAnalysis#getResult()}.
	 * @throws Exception
	 */
	protected abstract T analyze(IMonitor<T> monitor) throws Exception;

	@Override
	public final T execute(IMonitor<T> monitor) throws Exception {
		if (getSolver() == null) {
			return null;
		}
		getSolver().setConfiguration(ISolver.CONFIG_TIMEOUT, timeout);
		if (assumptions != null) {
			for (final int literal : assumptions.getLiterals()) {
				getSolver().push(getSolver().getProblem().getVariableAsNode(literal));
			}
		}
		// TODO SOLVER Sebastian Why set the assumption?
		// assumptions = new LiteralSet(solver.getAssignmentArray());
		timeoutOccured = false;

		monitor.checkCancel();
		try {
			result = analyze(monitor);
			return result;
		} catch (final Throwable e) {
			throw e;
		} finally {
			getSolver().popAll();
		}
	}

	@Override
	public final LiteralSet getAssumptions() {
		return assumptions;
	}

	public Random getRandom() {
		return random;
	}

	@Override
	public final AnalysisResult<T> getResult() {
		return new AnalysisResult<>(this.getClass().getName(), assumptions, result);
	}

	public int getTimeout() {
		return timeout;
	}

	public final boolean isThrowTimeoutException() {
		return throwTimeoutException;
	}

	public final boolean isTimeoutOccured() {
		return timeoutOccured;
	}

	/**
	 * This method can be used to indicate that a timeout occurred when executing the analysis.
	 *
	 * @throws RuntimeTimeoutException Whether a timeout occurs and {@link GeneralSolverAnalysis#throwTimeoutException} is true then a RuntimeTimeoutException
	 *         is thrown.
	 */
	protected final void reportTimeout() throws RuntimeTimeoutException {
		timeoutOccured = true;
		if (throwTimeoutException) {
			throw new RuntimeTimeoutException();
		}
	}

	@Override
	public final void setAssumptions(LiteralSet assumptions) {
		this.assumptions = assumptions;
	}

	/**
	 * Sets a new random instance.
	 *
	 * @param random
	 */
	public void setRandom(Random random) {
		this.random = random;
	}

	/**
	 * Determine whether the analysis should throw a {@link RuntimeTimeoutException} when a timeout occurs.
	 *
	 * @param throwTimeoutException
	 */
	public final void setThrowTimeoutException(boolean throwTimeoutException) {
		this.throwTimeoutException = throwTimeoutException;
	}

	/**
	 * Set the timeout for the solver in ms.
	 *
	 * @param timeout Timeout time in ms.
	 */
	public void setTimeout(int timeout) {
		this.timeout = timeout;
	}
}
