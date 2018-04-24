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

import org.prop4j.solver.FixedLiteralSelectionStrategy;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;
import org.prop4j.solver.VarOrderHeap2;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.core.Solver;

import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.mig.CollectingVisitor;
import de.ovgu.featureide.fm.core.configuration.mig.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.configuration.mig.Traverser;
import de.ovgu.featureide.fm.core.configuration.mig.Vertex;
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

	public ConditionallyCoreDeadAnalysisMIG(SatInstance satInstance, ModalImplicationGraph mig) {
		super(satInstance);
		this.mig = mig;
	}

	@Override
	public int[] analyze(IMonitor monitor) throws Exception {
		super.analyze(monitor);
		monitor.setRemainingWork(solver.getSatInstance().getNumberOfVariables() + 2);

		final Traverser traverser = mig.traverse();
		final int[] knownValues = new int[solver.getSatInstance().getNumberOfVariables()];

		if (assumptions != null) {
			for (final int assumption : assumptions) {
				final int var = Math.abs(assumption);
				knownValues[var - 1] = assumption;
				monitor.step(new IntermediateResult(var, Selection.UNDEFINED));
			}
			solver.getAssignment().ensure(assumptions.length + fixedVariables.length + 1);
		} else {
			solver.getAssignment().ensure(fixedVariables.length + 1);
		}

		for (final int fixedVar : fixedVariables) {
			final int var = Math.abs(fixedVar);
			knownValues[var - 1] = fixedVar;
			monitor.step(new IntermediateResult(var, Selection.UNDEFINED));
		}

		// get core / dead variables
		for (final Vertex vertex : mig.getAdjList()) {
			final byte core = vertex.getCore();
			final int var = vertex.getLiteral();
			if ((core != 0) && (var > 0)) {
				final int signedVar = core < 0 ? -var : var;
				knownValues[var - 1] = signedVar;
				monitor.step(new IntermediateResult(var, core < 0 ? Selection.UNSELECTED : Selection.SELECTED));
			}
		}

		traverser.setModel(knownValues);
		final CollectingVisitor visitor = new CollectingVisitor();
		for (int i = 0; i < newCount; i++) {
			traverser.traverse(fixedVariables[i], visitor);
		}
		final VecInt computedValues = visitor.getResult()[0];
		VecInt valuesToCompute = visitor.getResult()[1];

		monitor.setRemainingWork(valuesToCompute.size() + computedValues.size() + 3);

		for (int i = 0; i < computedValues.size(); i++) {
			final int computedVar = computedValues.get(i);
			final int var = Math.abs(computedVar);
			knownValues[var - 1] = computedVar;
			monitor.step(new IntermediateResult(var, computedVar < 0 ? Selection.UNSELECTED : Selection.SELECTED));
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

		solver.assignmentClear(0);
		for (final int var : knownValues) {
			if (var != 0) {
				solver.assignmentPush(var);
			}
		}
		monitor.checkCancel();

		if (!valuesToCompute.isEmpty()) {
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			final int[] unkownValues = solver.findModel();
			monitor.step();

			if (unkownValues != null) {
				solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
				final int[] model2 = solver.findModel();
				monitor.step();

				updateModel(unkownValues, model2);
				((Solver<?>) solver.getInternalSolver()).setOrder(new VarOrderHeap2(new FixedLiteralSelectionStrategy(unkownValues, true), solver.getOrder()));

				for (int k = 0; k < knownValues.length; k++) {
					final int var = knownValues[k];
					if ((var != 0)) {
						unkownValues[k] = 0;
					}
				}
				monitor.step();

				sat(unkownValues, valuesToCompute, monitor, traverser);
			}
		}
		return solver.getAssignmentArray(0, solver.getAssignment().size());
	}

	private void sat(int[] unkownValues, VecInt valuesToCalulate, IMonitor monitor, Traverser traverser) {
		final CollectingVisitor visitor = new CollectingVisitor();

		while (!valuesToCalulate.isEmpty()) {
			final int varX = valuesToCalulate.last();
			valuesToCalulate.pop();
			final int i = Math.abs(varX) - 1;
			if (unkownValues[i] == varX) {
				solver.assignmentPush(-varX);
				switch (solver.isSatisfiable()) {
				case FALSE:
					solver.assignmentReplaceLast(varX);
					unkownValues[i] = 0;
					monitor.step(new IntermediateResult(Math.abs(varX), varX < 0 ? Selection.UNSELECTED : Selection.SELECTED));
					traverser.traverseStrong(varX, visitor);
					final VecInt newFoundValues = visitor.getResult()[0];
					for (int j = 0; j < newFoundValues.size(); j++) {
						final int var = newFoundValues.get(j);
						if (unkownValues[Math.abs(var) - 1] != 0) {
							solver.assignmentPush(var);
							unkownValues[Math.abs(var) - 1] = 0;
							monitor.step(new IntermediateResult(Math.abs(var), var < 0 ? Selection.UNSELECTED : Selection.SELECTED));
						}
					}
					break;
				case TIMEOUT:
					solver.assignmentPop();
					unkownValues[Math.abs(varX) - 1] = 0;
					monitor.step(new IntermediateResult(Math.abs(varX), Selection.UNDEFINED));
					break;
				case TRUE:
					solver.assignmentPop();
					updateModel(unkownValues, solver.getModel());
					solver.shuffleOrder();
					break;
				}
			}
		}
	}

}
