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
import org.sat4j.specs.IteratorInt;

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
		this.traverser = featureGraph.getTraverser();
	}

	public DecisionPropagationAnalysisMIG(CNF satInstance, IModalImplicationGraph featureGraph) {
		super(satInstance);
		this.traverser = featureGraph.getTraverser();
	}

	public LiteralSet analyze(IMonitor monitor) throws Exception {
		if (changedVars == null) {
			traverser.markDefined(assumptions);
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
			traverser.markDefinedAndUndefined(new LiteralSet(Arrays.copyOf(defined.toArray(), defined.size())),
					new LiteralSet(Arrays.copyOf(undefined.toArray(), undefined.size())));
		}
		final VecInt selectedVars = traverser.getVariablesMarkedForSelection();
		final VecInt calculationVars = traverser.getVariablesMarkedForCalculation();

		for (IteratorInt it = selectedVars.iterator(); it.hasNext();) {
			solver.assignmentPush(it.next());
		}

		if (!calculationVars.isEmpty()) {
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			final int[] model1 = solver.findSolution();

			if (model1 != null) {
				solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
				final int[] model2 = solver.findSolution();

				SatUtils.updateSolution(model1, model2);
				for (IteratorInt it = selectedVars.iterator(); it.hasNext();) {
					model1[Math.abs(it.next()) - 1] = 0;
				}

				solver.setSelectionStrategy(model1, true);
				sat(model1, calculationVars);
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
					final int[] stronglyConnected = traverser.getStronglyConnected(varX).getLiterals();
					for (int literal : stronglyConnected) {
						final int j = Math.abs(literal) - 1;
						if (model1[j] != 0) {
							model1[j] = 0;
							solver.assignmentPush(literal);
						}
					}
					break;
				case TIMEOUT:
					reportTimeout();
					break;
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
