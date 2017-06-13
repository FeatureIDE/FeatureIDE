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
package de.ovgu.featureide.fm.core.analysis.cnf.generator;

import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.SatUtils;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds random solutions of propositional formulas.
 * 
 * @author Sebastian Krieter
 */
public class RandomConfigurationGenerator extends PairWiseConfigurationGenerator {

	private final int maxValue;

	public RandomConfigurationGenerator(CNF satInstance, int maxValue) {
		super(satInstance, 0);
		this.maxValue = maxValue;
	}

	@Override
	public List<LiteralSet> analyze(IMonitor monitor) throws Exception {
		time = System.nanoTime();
		solver.setSelectionStrategy(SelectionStrategy.RANDOM);

		for (int i = 0; i < maxValue; i++) {
			monitor.checkCancel();
			if (handleNewConfig(solver.findSolution())) {
				break;
			}
			solver.shuffleOrder();
		}

		return getConfigurations();
	}

	private boolean handleNewConfig(int[] curModel) {
		if (curModel == null) {
			return true;
		}
		final int partCount = count(curModel);
		final Configuration config = new Configuration(new LiteralSet(curModel), partCount - getLastCoverage(), partCount);

		addCombinationsFromModel(curModel);

		config.time = System.nanoTime() - time;
		q.offer(config);
		synchronized (tempConfigurationList) {
			tempConfigurationList.add(config);
		}
		time = System.nanoTime();

		try {
			solver.addClause(new LiteralSet(curModel).negate());
		} catch (RuntimeContradictionException e) {
			return true;
		}

		return false;
	}

}
