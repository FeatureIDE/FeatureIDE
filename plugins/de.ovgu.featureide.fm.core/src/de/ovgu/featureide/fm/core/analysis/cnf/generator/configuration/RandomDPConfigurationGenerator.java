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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Solution;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfiguration;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfigurationUtil;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class RandomDPConfigurationGenerator extends AConfigurationGenerator implements ITWiseConfigurationGenerator {

	protected final TWiseConfigurationUtil util;
	private final boolean allowDuplicates;

	public RandomDPConfigurationGenerator(CNF cnf, int maxSampleSize, boolean allowDuplicates) {
		super(cnf, maxSampleSize);

		this.allowDuplicates = allowDuplicates;

		util = new TWiseConfigurationUtil(cnf, solver, Collections.<TWiseConfiguration> emptyList());
		util.computeMIG();
	}

	@Override
	protected void generate(IMonitor monitor) throws Exception {

		final int iterations = 10000;
		final double[] ratio = new double[solver.getSatInstance().getVariables().size()];
		final AConfigurationGenerator gen = new RandomConfigurationGenerator(solver.getSatInstance(), iterations, false);
		final List<int[]> sample = LongRunningWrapper.runMethod(gen);
		for (final int[] solution : sample) {
			for (int i = 0; i < solution.length; i++) {
				if (solution[i] > 0) {
					ratio[i]++;
				}
			}
		}
		for (int i = 0; i < ratio.length; i++) {
			ratio[i] /= sample.size();
		}

		monitor.setRemainingWork(maxSampleSize);
		solver.setSelectionStrategy(SelectionStrategy.RANDOM);

		final List<Integer> variableList = new ArrayList<>();
		for (int i = 1; i <= solver.getSatInstance().getVariables().size(); i++) {
			variableList.add(i);
		}
//		Collections.shuffle(variableList, util.getRandom());
//		Collections.sort(variableList, new Comparator<Integer>() {
//			@Override
//			public int compare(Integer arg0, Integer arg1) {
//				final double dist0 = Math.abs(ratio[arg0 - 1] - 0.5);
//				final double dist1 = Math.abs(ratio[arg1 - 1] - 0.5);
//				return (int) Math.signum(dist0 - dist1);
//			}
//		});

		for (int i = 0; i < maxSampleSize; i++) {
			final TWiseConfiguration newConfiguration = new TWiseConfiguration(util);
			Collections.shuffle(variableList, util.getRandom());

			for (final Integer variable : variableList) {
				final boolean positive = util.getRandom().nextDouble() < ratio[variable - 1];
//				final boolean positive = util.getRandom().nextBoolean();
				final LiteralSet selection = new LiteralSet(positive ? variable : -variable);
				if (!newConfiguration.getSolution().hasConflicts(selection)) {
					select(newConfiguration, Deduce.DP, selection);
					newConfiguration.updateSolverSolutions();
				}
			}
			// TODO implement duplicate detection
			addResult(new Solution(newConfiguration.getSolution()));
			monitor.step();
		}
	}

	public boolean selectionPossibleSAT(final LiteralSet literals, final TWiseConfiguration configuration) {
		if (util.hasSolver()) {
			final ISatSolver localSolver = util.getSolver();
			localSolver.setSelectionStrategy(SelectionStrategy.RANDOM);
			final int orgAssignmentSize = configuration.setUpSolver(localSolver);
			try {
				final int[] configurationLiterals = configuration.getSolution().getLiterals();
				for (final int literal : literals.getLiterals()) {
					if (configurationLiterals[Math.abs(literal) - 1] == 0) {
						localSolver.assignmentPush(literal);
					}
				}
				if (orgAssignmentSize < localSolver.getAssignmentSize()) {
					if (localSolver.hasSolution() != SatResult.TRUE) {
						return false;
					} else {
						util.addSolverSolution(localSolver.getInternalSolution());
						localSolver.shuffleOrder(util.getRandom());
					}
				}
			} finally {
				localSolver.assignmentClear(orgAssignmentSize);
			}
		}
		return true;
	}

	protected void select(TWiseConfiguration solution, Deduce deduce, LiteralSet literals) {
		solution.setLiteral(literals.getLiterals());
		if (util.hasSolver()) {
			switch (deduce) {
			case AC:
				solution.autoComplete();
				break;
			case DP:
				solution.propagation();
				break;
			case NONE:
				break;
			}
		}
	}

	public TWiseConfigurationUtil getUtil() {
		return util;
	}

}
