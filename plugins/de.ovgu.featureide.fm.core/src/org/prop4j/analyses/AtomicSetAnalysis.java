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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds atomic sets.
 * 
 * @author Sebastian Krieter
 */
public class AtomicSetAnalysis extends AbstractAnalysis<List<List<Literal>>> {

	public AtomicSetAnalysis(ISatSolver solver) {
		super(solver);
	}

	@Override
	public List<List<Literal>> execute(IMonitor monitor) throws Exception {
		final List<int[]> solutions = new ArrayList<>();
		final List<List<Literal>> result = new ArrayList<>();

		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		int[] model1 = solver.findModel();
		solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
		int[] model2 = solver.findModel();
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

		if (model1 != null) {
			final byte[] done = new byte[model1.length];

			ArrayList<Literal> setList = new ArrayList<>();
			final int[] model1Copy = Arrays.copyOf(model1, model1.length);

			solutions.add(model1);
			solutions.add(model2);

			SatInstance.updateModel(model1Copy, model2);
			for (int i = 0; i < model1Copy.length; i++) {
				final int varX = model1Copy[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					switch (solver.sat()) {
					case FALSE:
						done[i] = 2;
						solver.assignmentPop();
						solver.assignmentPush(varX);
						setList.add(solver.getSatInstance().getLiteral(varX));
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.assignmentPop();
						model2 = solver.getModel();
						SatInstance.updateModel(model1Copy, model2);
						solutions.add(model2);
						solver.shuffleOrder();
						break;
					}
				}
			}
			result.add(setList);

			for (int i = 0; i < model1.length; i++) {
				if (done[i] == 0) {
					done[i] = 2;

					int c = 0;
					int[] xModel0 = Arrays.copyOf(model1, model1.length);

					final int mx0 = xModel0[i];
					solver.assignmentPush(mx0);

					setList = new ArrayList<>();
					setList.add(solver.getSatInstance().getLiteral(mx0));
					
					inner: for (int j = i + 1; j < xModel0.length; j++) {
						final int my0 = xModel0[j];
						if (my0 != 0 && done[j] == 0) {
							for (int k = 1; k < solutions.size(); k++) {
								final int[] solution = solutions.get(k);
								final int mxI = solution[i];
								final int myI = solution[j];
								if ((mx0 == mxI) != (my0 == myI)) {
									continue inner;
								}
							}
							
							solver.assignmentPush(-my0);

							switch (solver.sat()) {
							case FALSE:
								done[j] = 1;
								break;
							case TIMEOUT:
								break;
							case TRUE:
								final int[] lastModel = solver.getModel();
								SatInstance.updateModel(xModel0, lastModel);
								solutions.add(lastModel);
								updateSolver(c++);
								break;
							}
							solver.assignmentPop();
						}
					}

					solver.assignmentPop();
					solver.assignmentPush(-mx0);

					switch (solver.sat()) {
					case FALSE:
						break;
					case TIMEOUT:
						for (int j = i + 1; j < xModel0.length; j++) {
							done[j] = 0;
						}
						break;
					case TRUE:
						xModel0 = solver.getModel();
						break;
					}

					for (int j = i + 1; j < xModel0.length; j++) {
						if (done[j] == 1) {
							final int my0 = xModel0[j];
							if (my0 != 0) {
								solver.assignmentPush(-my0);

								switch (solver.sat()) {
								case FALSE:
									done[j] = 2;
									setList.add(solver.getSatInstance().getLiteral(-my0));
									break;
								case TIMEOUT:
									done[j] = 0;
									break;
								case TRUE:
									done[j] = 0;
									final int[] lastModel = solver.getModel();
									SatInstance.updateModel(xModel0, lastModel);
									solutions.add(lastModel);
									updateSolver(c++);
									break;
								}
								solver.assignmentPop();
							} else {
								done[j] = 0;
							}
						}
					}

					solver.assignmentPop();
					result.add(setList);
				}
			}
		}
		System.out.println(solutions.size());
		return result;
	}

	private void updateSolver(int c) {
		if ((c % 2 == 0)) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
		} else {
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			solver.shuffleOrder();
		}
	}

}
