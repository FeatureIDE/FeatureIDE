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
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.core.Solver;
import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Computes the number of valid solutions for the given {@link SatInstance}.
 *
 * @author Sebastian Krieter
 */
public class CountSolutionAnalysis extends AbstractAnalysis<Long> {

	public CountSolutionAnalysis(SatInstance satInstance) {
		this(satInstance, ISatSolver.DEFAULT_TIMEOUT);
	}

	public CountSolutionAnalysis(SatInstance satInstance, long globalTimeout) {
		super(createSolver(satInstance, globalTimeout));
	}

	private static BasicSolver createSolver(SatInstance satInstance, final long timeout) {
		try {
			return new BasicSolver(satInstance) {
				@Override
				protected Solver<?> initSolver() {
					final Solver<?> solver = super.initSolver();
					solver.setTimeoutMs(timeout);
					setGlobalTimeout(true);
					return solver;
				}
			};
		} catch (final ContradictionException e) {
			return null;
		}
	}

	@Override
	public Long analyze(IMonitor monitor) throws Exception {
		long lowerBound = 0;
		solver.setSelectionStrategy(SelectionStrategy.RANDOM);
		solutionLoop: while (true) {
			switch (solver.isSatisfiable()) {
			case TIMEOUT:
				lowerBound = -1 - lowerBound;
			case FALSE:
				break solutionLoop;
			case TRUE:
				lowerBound++;
				try {
					solver.getInternalSolver().addClause(new VecInt(SatInstance.negateModel(solver.getModel())));
				} catch (final ContradictionException e) {
					break solutionLoop;
				}
				solver.shuffleOrder();
				break;
			default:
				throw new RuntimeException();
			}
		}
		return lowerBound;
	}

}
