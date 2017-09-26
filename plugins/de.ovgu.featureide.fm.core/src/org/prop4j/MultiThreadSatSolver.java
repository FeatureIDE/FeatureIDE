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
package org.prop4j;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;

/**
 * SatSolver wrapper for multi-thread usage.
 *
 * @author Sebastian Krieter
 */
public class MultiThreadSatSolver {

	private static final class Solver {

		private final ISolver solver;
		private IVecInt backbone = new VecInt();

		public Solver(int numberOfVars, long timeout) {
			solver = SolverFactory.newDefault();
			solver.setTimeoutMs(timeout);
			solver.newVar(numberOfVars);
		}

		public boolean isSatisfiable() throws TimeoutException {
			return solver.isSatisfiable(backbone);
		}
	}

	private final Solver[] solvers;

	protected final Map<Object, Integer> varToInt = new HashMap<>();

	private int[] model = null;
	private boolean satisfiable = true;

	private final long timeout;

	private final Node node;

	private int[] literals;

	public MultiThreadSatSolver(Node node, long timeout, int numberOfSolvers, boolean createCNF) {
		readVars(node);

		this.timeout = timeout;
		this.node = createCNF ? node.toCNF() : node;

		solvers = new Solver[numberOfSolvers];
	}

	public boolean initSolver(int id) {
		solvers[id] = new Solver(varToInt.size(), timeout);
		addClauses(node.clone(), id);

		if (literals != null) {
			solvers[id].backbone = newCopiedVecInt(literals, 10);
		}

		if (id == 0) {
			try {
				satisfiable = solvers[0].isSatisfiable();
			} catch (final TimeoutException e) {
				satisfiable = false;
				Logger.logError(e);
			}

			synchronized (this) {
				if (satisfiable) {
					final int[] solverModel = solvers[0].solver.model();
					model = new int[solvers[0].solver.nVars()];
					System.arraycopy(solverModel, 0, model, 0, solverModel.length);
				}
				notifyAll();
			}
		} else {
			synchronized (this) {
				if (satisfiable && (model == null)) {
					try {
						this.wait();
					} catch (final InterruptedException e) {
						Logger.logError(e);
					}
				}
			}
		}

		return satisfiable;
	}

	private void readVars(Node node) {
		if (node instanceof Literal) {
			final Object var = ((Literal) node).var;
			if (!varToInt.containsKey(var)) {
				final int index = varToInt.size() + 1;
				varToInt.put(var, index);
			}
		} else {
			for (final Node child : node.getChildren()) {
				readVars(child);
			}
		}
	}

	private void addClauses(Node root, int id) {
		try {
			if (root instanceof And) {
				for (final Node node : root.getChildren()) {
					addClause(node, id);
				}
			} else {
				addClause(root, id);
			}
		} catch (final ContradictionException e) {
			satisfiable = false;
		}
	}

	private void addClause(Node node, int id) throws ContradictionException {
		if (node instanceof Or) {
			final int[] clause = new int[node.children.length];
			int i = 0;
			for (final Node child : node.getChildren()) {
				clause[i++] = getIntOfLiteral(child);
			}
			addClause(clause, id);
		} else {
			addClause(new int[] { getIntOfLiteral(node) }, id);
		}
	}

	private void addClause(int[] literals, int id) throws ContradictionException {
		solvers[id].solver.addClause(new VecInt(literals));
	}

	private VecInt newCopiedVecInt(int[] literals, int additionalSpace) {
		final int[] copiedLiterals = new int[literals.length + additionalSpace];
		System.arraycopy(literals, 0, copiedLiterals, 0, literals.length);
		final VecInt vecInt = new VecInt(copiedLiterals);
		vecInt.shrinkTo(literals.length);
		return vecInt;
	}

	private int getIntOfLiteral(Node node) {
		return getIntOfLiteral((Literal) node);
	}

	private int getIntOfLiteral(Literal node) {
		return node.positive ? varToInt.get(node.var) : -varToInt.get(node.var);
	}

	public void setLiterals(List<Literal> knownLiterals) {
		model = null;
		literals = new int[knownLiterals.size()];
		int i = 0;
		for (final Literal node : knownLiterals) {
			literals[i++] = getIntOfLiteral(node);
		}
	}

	public byte getValueOf(Literal literal, int solverIndex) {
		final int i = getIntOfLiteral(literal) - 1;
		return (model[i] != 0) ? getValueOf(i, solverIndex) : 0;
	}

	public boolean isFalse(Literal literal, int solverIndex) {
		final int i = getIntOfLiteral(literal) - 1;
		return (model[i] < 0) && (getValueOf(i, solverIndex) != 0);
	}

	public boolean isTrue(Literal literal, int solverIndex) {
		final int i = getIntOfLiteral(literal) - 1;
		return (model[i] > 0) && (getValueOf(i, solverIndex) != 0);
	}

	private byte getValueOf(int varIndex, int solverIndex) {
		if (satisfiable) {
			final int x = model[varIndex];
			if (x != 0) {
				final Solver solver = solvers[solverIndex];

				final int containsAt = solver.backbone.containsAt(x);
				final boolean isContained = containsAt >= 0;
				if (isContained) {
					solver.backbone.set(containsAt, 0);
				}

				solver.backbone.push(-x);
				try {
					if (solver.isSatisfiable()) {
						solver.backbone.pop();
						updateModel(solver.solver.model(), varIndex);
					} else {
						solver.backbone.pop();
						if (!isContained) {
							solver.backbone.push(x);
						}
						return (byte) Math.signum(x);
					}
				} catch (final TimeoutException e) {
					Logger.logError(e);
					solver.backbone.pop();
				} finally {
					if (isContained) {
						solver.backbone.set(containsAt, x);
					}
				}
			}
		}
		return 0;
	}

	private synchronized void updateModel(final int[] tempModel, int start) {
		for (int j = start; j < tempModel.length; j++) {
			if (model[j] != tempModel[j]) {
				model[j] = 0;
			}
		}
	}

}
