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
package org.prop4j.analyses.impl.general.sat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.impl.SolverManager;
import org.prop4j.solver.impl.SolverUtils;
import org.prop4j.solver.impl.sat4j.Sat4JSatSolver.SelectionStrategy;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.base.util.RingList;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds atomic sets.
 *
 * @author Sebastian Krieter
 */
public class AtomicSetAnalysis extends AbstractSatSolverAnalysis<List<LiteralSet>> {

	public AtomicSetAnalysis(ISatSolver solver) {
		super(solver);
	}

	public AtomicSetAnalysis(ISatProblem satInstance) {
		super(satInstance);
	}

	@Override
	protected List<LiteralSet> analyze(IMonitor<List<LiteralSet>> monitor) throws Exception {
		final List<LiteralSet> result = new ArrayList<>();

		solver.setConfiguration(ISatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.POSITIVE);
		final int[] model1 = SolverUtils.getIntModel(solver.findSolution());

		// solver.useSolutionTList(1000);
		final RingList<int[]> solutionList = new RingList<>(1000);

		if (model1 != null) {
			solver.setConfiguration(ISatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.NEGATIVE);
			final int[] model2 = SolverUtils.getIntModel(solver.findSolution());
			solver.setConfiguration(ISatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.POSITIVE);

			final byte[] done = new byte[model1.length];

			final int[] model1Copy = Arrays.copyOf(model1, model1.length);

			LiteralSet.resetConflicts(model1Copy, model2);
			for (int i = 0; i < model1Copy.length; i++) {
				final int varX = model1Copy[i];
				if (varX != 0) {
					solver.push(solver.getProblem().getVariableAsNode(-varX));

					switch (solver.isSatisfiable()) {
					case FALSE:
						done[i] = 2;
						solver.pop();
						solver.push(solver.getProblem().getVariableAsNode(varX));
						break;
					case TIMEOUT:
						solver.pop();
						reportTimeout();
						break;
					case TRUE:
						solutionList.add(SolverUtils.getIntModel(solver.getSolution()));
						solver.pop();
						LiteralSet.resetConflicts(model1Copy, SolverUtils.getIntModel(solver.getSolution()));
						// solver.shuffleOrder(random); Cannot shuffle for all solvers
						break;
					}
				}
			}
			result.add(new LiteralSet(solver.getIndexOfAssumptions()));
			solver.setConfiguration(ISatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.RANDOM);

			for (int i = 0; i < model1.length; i++) {
				if (done[i] == 0) {
					done[i] = 2;

					// int c = 0;
					int[] xModel0 = Arrays.copyOf(model1, model1.length);

					final int mx0 = xModel0[i];
					solver.push(solver.getProblem().getVariableAsNode(mx0));

					inner: for (int j = i + 1; j < xModel0.length; j++) {
						final int my0 = xModel0[j];
						if ((my0 != 0) && (done[j] == 0)) {
							for (int k = 1; k < solutionList.size(); k++) {
								final int[] solution = solutionList.get(k);
								final int mxI = solution[i];
								final int myI = solution[j];
								if ((mx0 == mxI) != (my0 == myI)) {
									continue inner;
								}
							}

							solver.push(solver.getProblem().getVariableAsNode(-my0));

							switch (solver.isSatisfiable()) {
							case FALSE:
								done[j] = 1;
								break;
							case TIMEOUT:
								reportTimeout();
								break;
							case TRUE:
								final int[] solutionNow = SolverUtils.getIntModel(solver.getSolution());
								solutionList.add(solutionNow);
								LiteralSet.resetConflicts(xModel0, solutionNow);
								// updateSolver(c++);
								// solver.shuffleOrder(random);
								break;
							}
							solver.pop();
						}
					}

					solver.pop();
					solver.push(solver.getProblem().getVariableAsNode(-mx0));

					switch (solver.isSatisfiable()) {
					case FALSE:
						break;
					case TIMEOUT:
						for (int j = i + 1; j < xModel0.length; j++) {
							done[j] = 0;
						}
						reportTimeout();
						break;
					case TRUE:
						xModel0 = SolverUtils.getIntModel(solver.getSolution());
						break;
					}

					for (int j = i + 1; j < xModel0.length; j++) {
						if (done[j] == 1) {
							final int my0 = xModel0[j];
							if (my0 != 0) {
								solver.push(solver.getProblem().getVariableAsNode(-my0));

								switch (solver.isSatisfiable()) {
								case FALSE:
									done[j] = 2;
									solver.pop();
									solver.push(solver.getProblem().getVariableAsNode(my0));
									break;
								case TIMEOUT:
									done[j] = 0;
									solver.pop();
									reportTimeout();
									break;
								case TRUE:
									done[j] = 0;
									LiteralSet.resetConflicts(xModel0, SolverUtils.getIntModel(solver.getSolution()));
									// updateSolver(c++);
									// solver.shuffleOrder(random);
									solver.pop();
									break;
								}
							} else {
								done[j] = 0;
							}
						}
					}

					result.add(new LiteralSet(solver.getIndexOfAssumptions()));
					solver.popAll();
				}
			}
		}
		return result;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.impl.general.sat.AbstractSatSolverAnalysis#initSolver(org.prop4j.solver.ISatProblem)
	 */
	@Override
	public ISatSolver initSolver(ISatProblem problem) {
		if (solver == null) {
			// Create new solver
			solver = SolverManager.getSelectedFeatureAttributeSolverFactory().getAnalysisSolver(problem);
		}
		return solver;
	}

}
