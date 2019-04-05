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
public class UniformRandomConfigurationGenerator extends AConfigurationGenerator {

	private Random rnd = new Random();
	private boolean allowDuplicates = true;
	private int sampleSize = 1000;

	public UniformRandomConfigurationGenerator(CNF cnf, int maxNumber) {
		super(cnf, maxNumber, true);
	}

	public UniformRandomConfigurationGenerator(CNF cnf, int maxNumber, boolean incremental) {
		super(cnf, maxNumber, incremental);
	}

	@Override
	protected void generate(IMonitor monitor) throws Exception {
		final AConfigurationGenerator gen = new RandomConfigurationGenerator(solver.getSatInstance(), sampleSize, false, rnd);
		final List<int[]> sample = LongRunningWrapper.runMethod(gen);

		monitor.setRemainingWork(maxSampleSize);
		solver.setSelectionStrategy(sample);

		for (int i = 0; i < maxSampleSize; i++) {
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

	public boolean isAllowDuplicates() {
		return allowDuplicates;
	}

	public void setAllowDuplicates(boolean allowDuplicates) {
		this.allowDuplicates = allowDuplicates;
	}

	public Random getRnd() {
		return rnd;
	}

	public int getSampleSize() {
		return sampleSize;
	}

	public void setRnd(Random rnd) {
		this.rnd = rnd;
	}

	public void setSampleSize(int sampleSize) {
		this.sampleSize = sampleSize;
	}

}
