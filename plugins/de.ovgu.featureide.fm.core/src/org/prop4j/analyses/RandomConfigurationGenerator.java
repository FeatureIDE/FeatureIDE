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

import java.util.List;

import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds random solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class RandomConfigurationGenerator extends PairWiseConfigurationGenerator {

	public RandomConfigurationGenerator(SatInstance satInstance, int maxNumber) {
		super(satInstance, maxNumber);
	}

	@Override
	public List<List<String>> analyze(IMonitor monitor) throws Exception {
		time = System.nanoTime();
		solver.setSelectionStrategy(SelectionStrategy.RANDOM);

		for (int i = 0; i < maxNumber; i++) {
			monitor.checkCancel();
			if (handleNewConfig(solver.findModel())) {
				break;
			}
			solver.shuffleOrder();
		}

		return getConfigurations();
	}

	private boolean handleNewConfig(int[] curModel) {
		if (curModel == null) {
			System.out.println("Found everything!");
			return true;
		}
		final int partCount = count(curModel);
		final Configuration config = new Configuration(curModel, partCount - getLastCoverage(), partCount);

		addCombinationsFromModel(curModel);

		config.time = System.nanoTime() - time;
		q.offer(config);
		synchronized (tempConfigurationList) {
			tempConfigurationList.add(config);
		}
		time = System.nanoTime();

		try {
			config.setBlockingClauseConstraint(solver.getInternalSolver().addBlockingClause(new VecInt(SatInstance.negateModel(curModel))));
		} catch (final ContradictionException e) {
			e.printStackTrace();
			System.out.println("Unsatisfiable1!");
			return true;
		}

		return false;
	}

}
