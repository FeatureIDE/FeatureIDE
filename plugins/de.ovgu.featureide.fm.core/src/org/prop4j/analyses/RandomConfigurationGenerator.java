/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import org.prop4j.solver.BasicSolver.SelectionStrategy;
import org.prop4j.solver.ISolverProvider;
import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Finds certain solutions of propositional formulas.
 * 
 * @author Sebastian Krieter
 */
public class RandomConfigurationGenerator extends PairWiseConfigurationGenerator {

	private final int maxValue;
	
	public RandomConfigurationGenerator(ISolverProvider solver, int maxValue) {
		super(solver, 0);
		this.maxValue = maxValue;
	}

	@Override
	public List<List<String>> execute(WorkMonitor monitor) throws Exception {
		time = System.nanoTime();
		final SatInstance satInstance = solver.getSatInstance();
		solver.setSelectionStrategy(SelectionStrategy.RANDOM);
		
		for (int i = 0; i < maxValue; i++) {
			handleNewConfig(solver.findModel(), satInstance);
			solver.shuffleOrder();
		}

		return getConfigurations();
	}

	private boolean handleNewConfig(int[] curModel, final SatInstance satInstance) {
		if (curModel == null) {
			System.out.println("Found everything!");
			return true;
		}
		final int partCount = count(curModel);
		final Configuration config = new Configuration(curModel, partCount - getLastCoverage(), partCount);

		addCombinationsFromModel(curModel);
		
		config.time = System.nanoTime() - time;
		q.offer(config);
		time = System.nanoTime();
		
		try {
			config.setBlockingClauseConstraint(solver.getSolver().addBlockingClause(new VecInt(SatInstance.negateModel(curModel))));
		} catch (ContradictionException e) {
			e.printStackTrace();
			System.out.println("Unsatisfiable1!");
			return true;
		}

		return false;
	}

}
