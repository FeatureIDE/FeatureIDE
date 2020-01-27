/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.mig.CollectingVisitor;
import de.ovgu.featureide.fm.core.analysis.mig.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.mig.Traverser;
import de.ovgu.featureide.fm.core.analysis.mig.Vertex;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 */
public class ConditionallyCoreDeadAnalysisMIG extends AConditionallyCoreDeadAnalysis {

	private final ModalImplicationGraph mig;

	public ConditionallyCoreDeadAnalysisMIG(ISatSolver solver, ModalImplicationGraph mig) {
		super(solver);
		this.mig = mig;
	}

	public ConditionallyCoreDeadAnalysisMIG(CNF satInstance, ModalImplicationGraph mig) {
		super(satInstance);
		this.mig = mig;
	}

	@Override
	public LiteralSet analyze(IMonitor<LiteralSet> monitor) throws Exception {
		super.analyze(monitor);
		monitor.setRemainingWork(solver.getSatInstance().getVariables().size() + 2);

		final Traverser traverser = mig.traverse();
		solver.asignmentEnsure(fixedVariables.length + 1);
		final int[] knownValues = new int[solver.getSatInstance().getVariables().size()];

		for (final int fixedVar : fixedVariables) {
			final int var = Math.abs(fixedVar);
			knownValues[var - 1] = fixedVar;
			monitor.step();
		}

		// get core / dead variables
		for (final Vertex vertex : mig.getAdjList()) {
			if (vertex.isCore()) {
				final int var = vertex.getVar();
				knownValues[var - 1] = var;
				monitor.step(new LiteralSet(var));
			}
		}

		traverser.setModel(knownValues);
		final CollectingVisitor visitor = new CollectingVisitor();
		traverser.setVisitor(visitor);
		for (int i = 0; i < newCount; i++) {
			traverser.traverse(fixedVariables[i]);
		}
		final VecInt computedValues = visitor.getResult()[0];
		VecInt valuesToCompute = visitor.getResult()[1];

		monitor.setRemainingWork(valuesToCompute.size() + computedValues.size() + 3);

		for (int i = 0; i < computedValues.size(); i++) {
			final int computedVar = computedValues.get(i);
			final int var = Math.abs(computedVar);
			knownValues[var - 1] = computedVar;
			monitor.step(new LiteralSet(computedVar));
		}

		if (variableOrder != null) {
			final VecInt sortedValuesToCalulate = new VecInt(valuesToCompute.size());
			for (int i = variableOrder.length - 1; i >= 0; i--) {
				final int var = variableOrder[i];
				if (valuesToCompute.contains(var)) {
					sortedValuesToCalulate.push(var);
				}
				if (valuesToCompute.contains(-var)) {
					sortedValuesToCalulate.push(-var);
				}
			}
			valuesToCompute = sortedValuesToCalulate;
		}

		for (final int var : knownValues) {
			if (var != 0) {
				solver.assignmentPush(var);
			}
		}
		monitor.checkCancel();

		if (!valuesToCompute.isEmpty()) {
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			final int[] unkownValues = solver.findSolution();
			monitor.step();

			if (unkownValues != null) {
				solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
				final int[] model2 = solver.findSolution();
				monitor.step();

				updateModel(unkownValues, model2);
				solver.setSelectionStrategy(unkownValues, true);

				for (int k = 0; k < knownValues.length; k++) {
					final int var = knownValues[k];
					if ((var != 0) && (unkownValues[k] != 0)) {
						unkownValues[k] = 0;
					}
				}
				monitor.step();

				sat(unkownValues, valuesToCompute, monitor, traverser);
			}
		}
		return new LiteralSet(solver.getAssignmentArray(0, solver.getAssignmentSize()));
	}

	private void sat(int[] unkownValues, VecInt valuesToCalulate, IMonitor<LiteralSet> monitor, Traverser traverser) {
		final CollectingVisitor visitor = new CollectingVisitor();
		traverser.setVisitor(visitor);

		while (!valuesToCalulate.isEmpty()) {
			final int varX = valuesToCalulate.last();
			valuesToCalulate.pop();
			final int i = Math.abs(varX) - 1;
			if (unkownValues[i] == varX) {
				solver.assignmentPush(-varX);
				switch (solver.hasSolution()) {
				case FALSE:
					solver.assignmentReplaceLast(varX);
					unkownValues[i] = 0;
					monitor.step(new LiteralSet(varX));
					traverser.traverseStrong(varX);
					final VecInt newFoundValues = visitor.getResult()[0];
					for (int j = 0; j < newFoundValues.size(); j++) {
						final int var = newFoundValues.get(j);
						solver.assignmentPush(var);
						unkownValues[Math.abs(var) - 1] = 0;
						monitor.step(new LiteralSet(var));
					}
					break;
				case TIMEOUT:
					solver.assignmentPop();
					unkownValues[Math.abs(varX) - 1] = 0;
					monitor.step();
					break;
				case TRUE:
					solver.assignmentPop();
					updateModel(unkownValues, solver.getSolution());
					solver.shuffleOrder(getRandom());
					break;
				}
			}
		}
	}

}
