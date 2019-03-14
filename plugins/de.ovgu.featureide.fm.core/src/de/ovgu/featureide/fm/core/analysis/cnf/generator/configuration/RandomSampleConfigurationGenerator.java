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

import java.util.List;
import java.util.Random;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.SatUtils;
import de.ovgu.featureide.fm.core.analysis.cnf.Solution;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class RandomSampleConfigurationGenerator extends AConfigurationGenerator {

	private final Random rnd;
	private final boolean allowDuplicates;

	public RandomSampleConfigurationGenerator(CNF cnf, int maxNumber, boolean allowDuplicates) {
		this(cnf, maxNumber, allowDuplicates, new Random());
	}

	public RandomSampleConfigurationGenerator(CNF cnf, int maxNumber, boolean allowDuplicates, Random rnd) {
		this(cnf, maxNumber, allowDuplicates, rnd, false);
	}

	public RandomSampleConfigurationGenerator(CNF cnf, int maxNumber, boolean allowDuplicates, boolean incremental) {
		this(cnf, maxNumber, allowDuplicates, new Random(), incremental);
	}

	public RandomSampleConfigurationGenerator(CNF cnf, int maxNumber, boolean allowDuplicates, Random rnd, boolean incremental) {
		super(cnf, maxNumber, incremental);
		this.allowDuplicates = allowDuplicates;
		this.rnd = rnd;
	}

	@Override
	protected void generate(IMonitor monitor) throws Exception {

		final int iterations = 1000;
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
		solver.setSelectionStrategy(ratio);

		for (int i = 0; i < maxSampleSize; i++) {
			solver.shuffleOrder(rnd);
			final int[] solution = solver.findSolution();
			if (solution == null) {
				break;
			}
			addResult(new Solution(solution));
			monitor.step();
			if (!allowDuplicates) {
				try {
					solver.addClause(new LiteralSet(SatUtils.negateSolution(solution)));
				} catch (final RuntimeContradictionException e) {
					break;
				}
			}
		}
	}

}
