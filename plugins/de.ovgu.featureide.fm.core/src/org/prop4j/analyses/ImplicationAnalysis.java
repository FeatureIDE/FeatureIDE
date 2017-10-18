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

import java.util.ArrayList;
import java.util.List;

import org.prop4j.solver.BasicSolver;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.base.util.RingList;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 */
public class ImplicationAnalysis extends AbstractAnalysis<List<int[]>> {

	private final List<int[]> pairs;

	public ImplicationAnalysis(SatInstance satInstance, List<int[]> pairs) {
		super(satInstance);
		this.pairs = pairs;
	}

	public ImplicationAnalysis(BasicSolver solver, List<int[]> pairs) {
		super(solver);
		this.pairs = pairs;
	}

	@Override
	public List<int[]> analyze(IMonitor monitor) throws Exception {
		final List<int[]> resultList = new ArrayList<>();

		if (pairs == null) {
			return resultList;
		}

		final RingList<int[]> solutionList = new RingList<>(Math.min(pairs.size(), ISatSolver.MAX_SOLUTION_BUFFER));

		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

		monitor.checkCancel();
		final int[] model1 = solver.findModel();

		if (model1 != null) {
			solutionList.add(model1);
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);

			monitor.checkCancel();
			final int[] model2 = solver.findModel();
			solutionList.add(model2);

			// if there are more negative than positive literals
			if ((model1.length - countNegative(model1)) < countNegative(model2)) {
				solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			}

			pairLoop: for (final int[] pair : pairs) {
				monitor.checkCancel();
				solutionLoop: for (final int[] is : solutionList) {
					for (final int i : pair) {
						if (is[Math.abs(i) - 1] == i) {
							continue solutionLoop;
						}
					}
					continue pairLoop;
				}
				for (final int i : pair) {
					solver.assignmentPush(-i);
				}
				switch (solver.isSatisfiable()) {
				case FALSE:
					resultList.add(pair);
					break;
				case TIMEOUT:
					break;
				case TRUE:
					solutionList.add(solver.getModel());
					solver.shuffleOrder();
					break;
				}
				for (int i = 0; i < pair.length; i++) {
					solver.assignmentPop();
				}
			}
		}

		return resultList;
	}

	private static int countNegative(int[] model) {
		int count = 0;
		for (int i = 0; i < model.length; i++) {
			count += model[i] >>> (Integer.SIZE - 1);
		}
		return count;
	}

}
