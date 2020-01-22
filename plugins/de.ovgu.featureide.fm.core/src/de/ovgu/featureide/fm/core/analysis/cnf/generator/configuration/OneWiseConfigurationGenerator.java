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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import java.util.List;

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.IInternalVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Generates configurations for a given propositional formula such that one-wise feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class OneWiseConfigurationGenerator extends AConfigurationGenerator implements ITWiseConfigurationGenerator {

	public static enum CoverStrategy {
		POSITIVE, NEGATIVE
	}

	private CoverStrategy coverStrategy = CoverStrategy.NEGATIVE;

	private int[] variables;

	public OneWiseConfigurationGenerator(ISatSolver solver) {
		this(solver, null);
	}

	public OneWiseConfigurationGenerator(CNF satInstance) {
		this(satInstance, null);
	}

	public OneWiseConfigurationGenerator(CNF satInstance, int[] features) {
		super(satInstance);
		setFeatures(features);
	}

	public OneWiseConfigurationGenerator(ISatSolver solver, int[] features) {
		super(solver);
		setFeatures(features);
	}

	public int[] getFeatures() {
		return variables;
	}

	public void setFeatures(int[] features) {
		variables = features;
	}

	public CoverStrategy getCoverMode() {
		return coverStrategy;
	}

	public void setCoverMode(CoverStrategy coverStrategy) {
		this.coverStrategy = coverStrategy;
	}

	@Override
	protected void generate(IMonitor<List<LiteralSet>> monitor) throws Exception {
		final int initialAssignmentLength = solver.getAssignmentSize();

		switch (coverStrategy) {
		case NEGATIVE:
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			break;
		case POSITIVE:
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			break;
		default:
			throw new RuntimeException("Unknown " + CoverStrategy.class.getName() + ": " + coverStrategy);
		}

		if (solver.hasSolution() == SatResult.TRUE) {
			final VecInt variablesToCover = new VecInt();

			if (variables != null) {
				for (int i = 0; i < variables.length; i++) {
					final int var = variables[i];
					if (var > 0) {
						variablesToCover.push(var);
					}
				}
			}
			final IInternalVariables internalVariables = solver.getSatInstance().getInternalVariables();

			while (!variablesToCover.isEmpty()) {
				boolean firstVar = true;
				int[] lastSolution = null;
				for (int i = variablesToCover.size() - 1; i >= 0; i--) {
					int var = variablesToCover.get(i);
					if (var == 0) {
						continue;
					}

					switch (coverStrategy) {
					case NEGATIVE:
						var = -var;
						break;
					case POSITIVE:
						break;
					default:
						throw new RuntimeException("Unknown " + CoverStrategy.class.getName() + ": " + coverStrategy);
					}

					solver.assignmentPush(var);
					switch (solver.hasSolution()) {
					case FALSE:
						solver.assignmentReplaceLast(var);
						if (firstVar) {
							variablesToCover.set(i, 0);
						}
						break;
					case TIMEOUT:
						solver.assignmentPop();
						variablesToCover.set(i, 0);
						break;
					case TRUE:
						lastSolution = solver.getSolution();
						switch (coverStrategy) {
						case NEGATIVE:
							for (int j = i; j < variablesToCover.size(); j++) {
								if (lastSolution[internalVariables.convertToInternal(Math.abs(var)) - 1] < 0) {
									variablesToCover.set(i, 0);
								}
							}
							break;
						case POSITIVE:
							for (int j = i; j < variablesToCover.size(); j++) {
								if (lastSolution[internalVariables.convertToInternal(Math.abs(var)) - 1] > 0) {
									variablesToCover.set(i, 0);
								}
							}
							break;
						default:
							throw new RuntimeException("Unknown " + CoverStrategy.class.getName() + ": " + coverStrategy);
						}
						firstVar = false;
						break;
					}
				}

				if (lastSolution != null) {
					addResult(new LiteralSet(lastSolution, LiteralSet.Order.INDEX, false));
				}
				solver.assignmentClear(initialAssignmentLength);

				while (!variablesToCover.isEmpty()) {
					final int var = variablesToCover.last();
					if (var == 0) {
						variablesToCover.pop();
					} else {
						break;
					}
				}
			}

		}
	}

}
