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

import java.util.Arrays;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet.Order;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ModifiableSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 */
public class CoreDeadAnalysis extends AVariableAnalysis<LiteralSet> {

	public CoreDeadAnalysis(ISatSolver solver) {
		this(solver, null);
	}

	public CoreDeadAnalysis(CNF satInstance) {
		this(satInstance, null);
	}

	public CoreDeadAnalysis(CNF satInstance, LiteralSet variables) {
		super(satInstance);
		this.variables = variables;
	}

	public CoreDeadAnalysis(ISatSolver solver, LiteralSet variables) {
		super(solver);
		this.variables = variables;
	}

	@Override
	public LiteralSet analyze(IMonitor<LiteralSet> monitor) throws Exception {
		return analyze1(monitor);
	}

	@Override
	protected ISatSolver initSolver(CNF satInstance) {
		try {
			return new ModifiableSatSolver(satInstance);
		} catch (final RuntimeContradictionException e) {
			return null;
		}
	}

	public LiteralSet analyze2(IMonitor<LiteralSet> monitor) throws Exception {
		final int initialAssignmentLength = solver.getAssignmentSize();
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		int[] model1 = solver.findSolution();

		if (model1 != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			final int[] model2 = solver.findSolution();

			if (variables != null) {
				final int[] model3 = new int[model1.length];
				for (int i = 0; i < variables.getLiterals().length; i++) {
					final int index = variables.getLiterals()[i] - 1;
					if (index >= 0) {
						model3[index] = model1[index];
					}
				}
				model1 = model3;
			}

			for (int i = 0; i < initialAssignmentLength; i++) {
				model1[Math.abs(solver.assignmentGet(i)) - 1] = 0;
			}

			LiteralSet.resetConflicts(model1, model2);
			solver.setSelectionStrategy(model1,
					model1.length > (new LiteralSet(model2, Order.INDEX, false).countNegative() + new LiteralSet(model1, Order.INDEX, false).countNegative()));

			vars = new VecInt(model1.length);
			split(model1, 0, model1.length);
		}
		return new LiteralSet(solver.getAssignmentArray(initialAssignmentLength, solver.getAssignmentSize()));
	}

	VecInt vars;

	private void split(int[] model, int start, int end) {
		vars.clear();
		for (int j = start; j < end; j++) {
			final int var = model[j];
			if (var != 0) {
				vars.push(-var);
			}
		}
		switch (vars.size()) {
		case 0:
			return;
		case 1:
			test(model, 0);
			break;
		case 2:
			test(model, 0);
			test(model, 1);
			break;
		default:
			try {
				solver.addInternalClause(new LiteralSet(Arrays.copyOf(vars.toArray(), vars.size())));
				switch (solver.hasSolution()) {
				case FALSE:
					foundVariables(model, vars);
					// solver.removeLastClause();
					break;
				case TIMEOUT:
					reportTimeout();
					// solver.removeLastClause();
					break;
				case TRUE:
					LiteralSet.resetConflicts(model, solver.getSolution());
					solver.shuffleOrder(getRandom());

					final int halfLength = (end - start) / 2;
					if (halfLength > 0) {
						split(model, start + halfLength, end);
						split(model, start, start + halfLength);
					}
					break;
				}
				solver.removeLastClause();
			} catch (final RuntimeContradictionException e) {
				foundVariables(model, vars);
			}
			break;
		}
	}

	private void test(int[] model, int i) {
		final int var = vars.get(i);
		solver.assignmentPush(var);
		switch (solver.hasSolution()) {
		case FALSE:
			solver.assignmentReplaceLast(-var);
			model[Math.abs(var) - 1] = 0;
			break;
		case TIMEOUT:
			solver.assignmentPop();
			reportTimeout();
			break;
		case TRUE:
			solver.assignmentPop();
			LiteralSet.resetConflicts(model, solver.getSolution());
			solver.shuffleOrder(getRandom());
			break;
		}
	}

	private void foundVariables(int[] model, VecInt vars) {
		for (final IteratorInt iterator = vars.iterator(); iterator.hasNext();) {
			final int var = iterator.next();
			solver.assignmentPush(-var);
			model[Math.abs(var) - 1] = 0;
		}
	}

	public LiteralSet analyze1(IMonitor<LiteralSet> monitor) throws Exception {
		final int initialAssignmentLength = solver.getAssignmentSize();
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		int[] model1 = solver.findSolution();

		if (model1 != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			final int[] model2 = solver.findSolution();

			if (variables != null) {
				final int[] model3 = new int[model1.length];
				for (int i = 0; i < variables.getLiterals().length; i++) {
					final int index = variables.getLiterals()[i] - 1;
					if (index >= 0) {
						model3[index] = model1[index];
					}
				}
				model1 = model3;
			}

			for (int i = 0; i < initialAssignmentLength; i++) {
				model1[Math.abs(solver.assignmentGet(i)) - 1] = 0;
			}

			LiteralSet.resetConflicts(model1, model2);
			solver.setSelectionStrategy(model1,
					model1.length > (new LiteralSet(model2, Order.INDEX, false).countNegative() + new LiteralSet(model1, Order.INDEX, false).countNegative()));

			for (int i = 0; i < model1.length; i++) {
				final int varX = model1[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					switch (solver.hasSolution()) {
					case FALSE:
						solver.assignmentReplaceLast(varX);
						monitor.invoke(new LiteralSet(varX));
						break;
					case TIMEOUT:
						solver.assignmentPop();
						reportTimeout();
						break;
					case TRUE:
						solver.assignmentPop();
						LiteralSet.resetConflicts(model1, solver.getSolution());
						solver.shuffleOrder(getRandom());
						break;
					}
				}
			}
		}

		return new LiteralSet(solver.getAssignmentArray(initialAssignmentLength, solver.getAssignmentSize()));
	}

}
