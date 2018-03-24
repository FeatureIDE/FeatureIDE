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

import java.util.ArrayList;
import java.util.Collections;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatResult;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.impl.SolverUtils;

import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Represents an analysis that can be solved either by SMT or SAT solvers.
 *
 * @author Joshua Sprey
 */
public abstract class GeneralSolverAnalysis<T> implements ISolverAnalysis<T>, LongRunningMethod<T> {

	protected ISolver solver;
	public long solveTime = 0;
	public long editTime = 0;
	public long gesamtTime = 0;

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
		monitor.checkCancel();
		try {
			final T value = analyze(monitor);
			gesamtTime = solveTime + editTime;
			return value;
		} catch (final Throwable e) {
			throw e;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.ISolverAnalysis#analyze(de.ovgu.featureide.fm.core.job.monitor.IMonitor)
	 */
	@Override
	public T analyze(IMonitor monitor) {
		return null;
	}

	public Literal getLiteralFromIndex(int index) {
		final Object variable = solver.getProblem().getVariableOfIndex(Math.abs(index));
		final Literal literal = new Literal(variable, index > 0);
		return literal;
	}

	public int[] getIntegerAssumptions() {
		final ArrayList<Integer> solution = new ArrayList<>();
		Node currentNode = solver.pop();
		while (currentNode != null) {
			if (currentNode instanceof Literal) {
				final Literal literal = (Literal) currentNode;
				solution.add(solver.getProblem().getSignedIndexOfVariable(literal));
				currentNode = solver.pop();
			}
		}
		Collections.reverse(solution);

		return SolverUtils.getIntModel((Integer[]) solution.toArray(new Integer[solution.size()]));
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.ISolverAnalysis#getSolver()
	 */
	@Override
	public ISolver getSolver() {
		return solver;
	}

	protected ISatResult solverSatisfiable() {
		final long time = System.currentTimeMillis();
		final ISatResult result = solver.isSatisfiable();
		solveTime += (System.currentTimeMillis() - time);
		return result;
	}

	protected void solverPush(Node... node) throws ContradictionException {
		final long time = System.currentTimeMillis();
		solver.push(node);
		editTime += (System.currentTimeMillis() - time);
	}

	protected void solverPop() {
		final long time = System.currentTimeMillis();
		solver.pop();
		editTime += (System.currentTimeMillis() - time);
	}

	protected void solverPop(int count) {
		final long time = System.currentTimeMillis();
		solver.pop(count);
		editTime += (System.currentTimeMillis() - time);
	}

}
