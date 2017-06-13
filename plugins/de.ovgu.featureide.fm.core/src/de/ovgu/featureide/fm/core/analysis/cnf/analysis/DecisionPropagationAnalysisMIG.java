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
package de.ovgu.featureide.fm.core.analysis.cnf.analysis;

import java.util.Arrays;

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.SatUtils;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.base.IModalImplicationGraph;
import de.ovgu.featureide.fm.core.base.IModalImplicationGraph.ITraverser;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 * 
 * @author Sebastian Krieter
 */
public class DecisionPropagationAnalysisMIG extends AbstractAnalysis<LiteralSet> {

	private final ITraverser traverser;

	private int[] changedVars;

	public DecisionPropagationAnalysisMIG(ISatSolver solver, IModalImplicationGraph featureGraph) {
		super(solver);
		this.traverser = featureGraph.traverse();
	}

	public DecisionPropagationAnalysisMIG(CNF satInstance, IModalImplicationGraph featureGraph) {
		super(satInstance);
		this.traverser = featureGraph.traverse();
	}

	public LiteralSet analyze(IMonitor monitor) throws Exception {
		final int[] modelForDefinedVariables = new int[solver.getSatInstance().getVariables().size()];
		for (int i = 0; i < assumptions.size(); i++) {
			final int var = assumptions.getLiterals()[i];
			final int j = Math.abs(var) - 1;
			modelForDefinedVariables[j] = var;
		}

		traverser.init(modelForDefinedVariables);
		if (changedVars == null) {
			traverser.traverseDefined(assumptions);
		} else {
			VecInt defined = new VecInt();
			VecInt undefined = new VecInt();
			outer: for (int i = 0; i < changedVars.length; i++) {
				final int changedVar = changedVars[i];
				for (int assumption : assumptions.getLiterals()) {
					if (Math.abs(assumption) == changedVar) {
						defined.push(assumption);
						continue outer;
					}
				}
				undefined.push(changedVar);
			}
			traverser.traverseDefined(new LiteralSet(Arrays.copyOf(defined.toArray(), defined.size())));
			traverser.traverseUndefined(Arrays.copyOf(undefined.toArray(), undefined.size()));
		}
		final VecInt v = traverser.getRelevantVariables();

		for (int k = 0; k < modelForDefinedVariables.length; k++) {
			final int var = modelForDefinedVariables[k];
			if (var != 0) {
				solver.assignmentPush(var);
			}
		}

		if (!v.isEmpty()) {
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			final int[] model1 = solver.findSolution();

			if (model1 != null) {
				solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
				final int[] model2 = solver.findSolution();

				SatUtils.updateSolution(model1, model2);
				solver.setSelectionStrategy(model1, true);
				for (int k = 0; k < modelForDefinedVariables.length; k++) {
					final int var = modelForDefinedVariables[k];
					if (var != 0) {
						model1[Math.abs(var) - 1] = 0;
					}
				}

				sat(model1, v);
			}
		}
		return new LiteralSet(solver.getAssignmentArray(assumptions.size(), solver.getAssignmentSize()));
	}

	private void sat(int[] model1, VecInt v) {
		while (!v.isEmpty()) {
			final int varX = v.get(v.size() - 1);
			v.pop();
			final int i = Math.abs(varX) - 1;
			if (model1[i] == varX) {
				solver.assignmentPush(-varX);
				switch (solver.hasSolution()) {
				case FALSE:
					solver.assignmentReplaceLast(varX);
					model1[i] = 0;
					final VecInt newVars = traverser.traverse2(varX, model1);
					for (int j = 0; j < newVars.size(); j++) {
						solver.assignmentPush(newVars.get(i));
					}
					break;
				case TIMEOUT:
					throw new RuntimeException();
				case TRUE:
					solver.assignmentPop();
					SatUtils.updateSolution(model1, solver.getSolution());
					solver.shuffleOrder();
					break;
				}
			}
		}
	}

	public int[] getChanged() {
		return changedVars;
	}

	public void setChanged(int... changed) {
		this.changedVars = changed;
	}

}
