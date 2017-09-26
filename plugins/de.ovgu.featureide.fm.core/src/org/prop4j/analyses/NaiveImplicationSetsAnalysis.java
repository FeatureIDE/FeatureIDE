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

import java.util.Arrays;
import java.util.HashMap;

import org.prop4j.analyses.ImplicationSetsAnalysis.Relationship;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Creates a complete implication graph.</br> This class is only for benchmark purposes. Uses {@link ImplicationSetsAnalysis} instead.
 *
 * @author Sebastian Krieter AtomicSetAnalysis
 */
public class NaiveImplicationSetsAnalysis extends AbstractAnalysis<HashMap<Relationship, Relationship>> {

	private static final byte BIT_11 = 1 << 3;
	private static final byte BIT_10 = 1 << 2;
	private static final byte BIT_01 = 1 << 1;
	private static final byte BIT_00 = 1 << 0;

	public NaiveImplicationSetsAnalysis(ISatSolver solver) {
		super(solver);
	}

	public NaiveImplicationSetsAnalysis(SatInstance satInstance) {
		super(satInstance);
	}

	@Override
	public HashMap<Relationship, Relationship> analyze(IMonitor monitor) throws Exception {
		final HashMap<Relationship, Relationship> relationSet = new HashMap<>();

		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		final int[] model1 = solver.findModel();

		// satisfiable?
		if (model1 != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			int[] model2 = solver.findModel();
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

			// find core/dead features
			final byte[] done = new byte[model1.length];

			final int[] model1Copy = Arrays.copyOf(model1, model1.length);

			SatInstance.updateModel(model1Copy, model2);
			for (int i = 0; i < model1Copy.length; i++) {
				final int varX = model1Copy[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					switch (solver.isSatisfiable()) {
					case FALSE:
						done[i] = 2;
						solver.assignmentReplaceLast(varX);
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.assignmentPop();
						model2 = solver.getModel();
						SatInstance.updateModel(model1Copy, model2);
						solver.shuffleOrder();
						break;
					}
				}
			}

			for (int i = 0; i < model1.length; i++) {
				if (done[i] != 0) {
					continue;
				}
				final int varX = Math.abs(model1[i]);
				testCombinations(relationSet, model1, done, i, varX);
				testCombinations(relationSet, model1, done, i, -varX);
			}
		}
		return relationSet;
	}

	private void testCombinations(final HashMap<Relationship, Relationship> relationSet, int[] model1, final byte[] done, int i, final int varX) {
		solver.assignmentPush(varX);
		for (int j = i + 1; j < model1.length; j++) {
			if (done[j] != 0) {
				continue;
			}
			final int varY = Math.abs(model1[j]);
			testCombination(relationSet, varX, varY);
			testCombination(relationSet, varX, -varY);
		}
		solver.assignmentPop();
	}

	private void testCombination(final HashMap<Relationship, Relationship> relationSet, final int varX, final int varY) {
		solver.assignmentPush(-varY);
		switch (solver.isSatisfiable()) {
		case FALSE:
			addRelation(relationSet, varX, varY);
			break;
		case TIMEOUT:
			throw new RuntimeException();
		case TRUE:
			break;
		}
		solver.assignmentPop();
	}

	private void addRelation(final HashMap<Relationship, Relationship> relationSet, final int mx0, final int my0) {
		final Relationship newRelationship = new Relationship(Math.abs(mx0), Math.abs(my0));
		Relationship curRelationship = relationSet.get(newRelationship);
		if (curRelationship == null) {
			relationSet.put(newRelationship, newRelationship);
			curRelationship = newRelationship;
		}
		curRelationship.addRelation(mx0 > 0 ? (my0 > 0 ? BIT_11 : BIT_10) : (my0 > 0 ? BIT_01 : BIT_00));
	}

}
