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
package org.prop4j.analyses.impl.general;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.analyses.GeneralSolverAnalysis;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.impl.SolverUtils;
import org.prop4j.solver.impl.sat4j.Sat4jSatSolver;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class CoreDeadAnalysis extends GeneralSolverAnalysis<int[]> {

	public CoreDeadAnalysis(ISolver solver) {
		super(solver);
	}

	public CoreDeadAnalysis(ISolver solver, int[] features) {
		super(solver);
		setFeatures(features);
	}

	private int[] features;

	@Override
	public int[] analyze(IMonitor monitor) {
		HashMap<String, Object> config = new HashMap<>();
		config.put(Sat4jSatSolver.CONFIG_SELECTION_STRATEGY, Sat4jSatSolver.SelectionStrategy.POSITIVE);
		solver.setConfiguration(config);
		int[] model1 = SolverUtils.getIntModel(solver.findSolution());

		if (model1 != null) {
			config = new HashMap<>();
			config.put(Sat4jSatSolver.CONFIG_SELECTION_STRATEGY, Sat4jSatSolver.SelectionStrategy.NEGATIVE);
			solver.setConfiguration(config);
			final int[] model2 = SolverUtils.getIntModel(solver.findSolution());

			if (features != null) {
				final int[] model3 = new int[model1.length];
				for (int i = 0; i < features.length; i++) {
					final int index = features[i] - 1;
					if (index >= 0) {
						model3[index] = model1[index];
					}
				}
				model1 = model3;
			}

			SolverUtils.updateModel(model1, model2);

			for (int i = 0; i < model1.length; i++) {
				final int varX = model1[i];
				if (varX != 0) {
					solver.push(getLiteralFromIndex(-varX));
					switch (solver.isSatisfiable()) {
					case FALSE:
						solver.pop();
						solver.push(getLiteralFromIndex(varX));
						monitor.invoke(varX);
						break;
					case TIMEOUT:
						solver.pop();
						break;
					case TRUE:
						solver.pop();
						SolverUtils.updateModel(model1, SolverUtils.getIntModel(solver.getSoulution()));
						// solver.shuffleOrder();
						break;
					}
				}
			}
		}

		final ArrayList<Integer> solution = new ArrayList<>();
		Node currentNode = solver.pop();
		while (currentNode != null) {
			if (currentNode instanceof Literal) {
				final Literal literal = (Literal) currentNode;
				solution.add(solver.getProblem().getSignedIndexOfVariable(literal));
				currentNode = solver.pop();
			}
		}
		Collections.reverse(solution);

		return SolverUtils.getIntModel((Integer[]) solution.toArray(new Integer[solution.size()]));
	}

	public int[] getFeatures() {
		return features;
	}

	public void setFeatures(int[] features) {
		this.features = features;
	}

	public Literal getLiteralFromIndex(int index) {
		final Object variable = solver.getProblem().getVariableOfIndex(Math.abs(index));
		final Literal literal = new Literal(variable, index > 0);
		return literal;
	}

}
