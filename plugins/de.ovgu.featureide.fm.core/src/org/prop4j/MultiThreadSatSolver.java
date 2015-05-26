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

import de.ovgu.featureide.fm.core.FMCorePlugin;

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
//	protected final ArrayList<Object> intToVar = new ArrayList<>();

	private int[] model = null;
	private boolean satisfiable = false;

	public MultiThreadSatSolver(Node node, long timeout, int numberOfSolvers) {
		readVars(node);

		solvers = new Solver[numberOfSolvers];
		for (int i = 0; i < numberOfSolvers; i++) {
			solvers[i] = new Solver(varToInt.size(), timeout);
		}
		addClauses(node.toCNF());
	}

	private void readVars(Node node) {
		if (node instanceof Literal) {
			final Object var = ((Literal) node).var;
			if (!varToInt.containsKey(var)) {
				final int index = varToInt.size() + 1;
				varToInt.put(var, index);
//				intToVar.add(var);
			}
		} else {
			for (Node child : node.getChildren()) {
				readVars(child);
			}
		}
	}

	private void addClauses(Node root) {
		try {
			if (root instanceof And) {
				for (Node node : root.getChildren()) {
					addClause(node);
				}
			} else {
				addClause(root);
			}
		} catch (ContradictionException e) {
			satisfiable = false;
		}
	}

	private void addClause(Node node) throws ContradictionException {
		if (node instanceof Or) {
			final int[] clause = new int[node.children.length];
			int i = 0;
			for (Node child : node.getChildren()) {
				clause[i++] = getIntOfLiteral(child);
			}
			addClause(clause);
		} else {
			addClause(new int[] { getIntOfLiteral(node) });
		}
	}

	private void addClause(int[] literals) throws ContradictionException {
		for (int j = 0; j < solvers.length - 1; j++) {
			solvers[j].solver.addClause(newCopiedVecInt(literals));
		}
		solvers[solvers.length - 1].solver.addClause(new VecInt(literals));
	}

	private VecInt newCopiedVecInt(int[] literals) {
		return newCopiedVecInt(literals, 0);
	}

	private VecInt newCopiedVecInt(int[] literals, int additionalSpace) {
		int[] copiedLiterals = new int[literals.length + additionalSpace];
		System.arraycopy(literals, 0, copiedLiterals, 0, literals.length);
		return new VecInt(copiedLiterals);
	}

	private int getIntOfLiteral(Node node) {
		return getIntOfLiteral((Literal) node);
	}

	private int getIntOfLiteral(Literal node) {
		return node.positive ? varToInt.get(node.var) : -varToInt.get(node.var);
	}

	//	public List<Literal> knownValues(Literal... tempNodes) {
	//		return knownValues(ValueType.ALL, tempNodes);
	//	}
	//
	//	public List<Literal> knownValues(ValueType vt, Literal... tempNodes) {
	//		if (!contradiction) {
	//			final IVecInt backbone = new VecInt();
	//			for (int i = 0; i < tempNodes.length; i++) {
	//				backbone.push(getIntOfLiteral(tempNodes[i]));
	//			}
	//
	//			boolean satisfiable = false;
	//			try {
	//				satisfiable = solver.isSatisfiable(backbone);
	//			} catch (TimeoutException e) {
	//				FMCorePlugin.getDefault().logError(e);
	//			}
	//			if (satisfiable) {
	//				final byte[] b = new byte[solver.nVars()];
	//				final int[] model = solver.model();
	//				for (int i = 0; i < model.length; i++) {
	//					b[i] = (byte) Math.signum(model[i]);
	//				}
	//				for (int i = 0; i < model.length; i++) {
	//					if (b[i] == 0) {
	//						continue;
	//					}
	//					final int x = model[i];
	//					if ((x * vt.factor) >= 0) {
	//						backbone.push(-x);
	//						try {
	//							if (solver.isSatisfiable(backbone)) {
	//								backbone.pop();
	//								final int[] tempModel = solver.model();
	//								for (int j = i + 1; j < tempModel.length; j++) {
	//									if (b[j] != (byte) Math.signum(tempModel[j])) {
	//										b[j] = 0;
	//									}
	//								}
	//							} else {
	//								backbone.pop().push(x);
	//							}
	//						} catch (TimeoutException e) {
	//							FMCorePlugin.getDefault().logError(e);
	//							backbone.pop();
	//						}
	//					}
	//				}
	//
	//				for (int i = 0; i < tempNodes.length; i++) {
	//					backbone.delete(i);
	//				}
	//				return convertToNodes(backbone);
	//			}
	//		}
	//		return Collections.emptyList();
	//	}

	//TODO AtomicSets
	//	public List<List<Literal>> atomicSets() {
	//		if (satisfiable) {
	//			final List<List<Literal>> result = new ArrayList<>();
	//			result.add(new ArrayList<Literal>());
	//			result.add(new ArrayList<Literal>());
	//
	//			final IVecInt backbone = new VecInt();
	//			final int[] model = solver.model();
	//			final byte[] done = new byte[model.length];
	//
	//			for (int i = 0; i < model.length; i++) {
	//				final int x = model[i];
	//				if (!sat(backbone, -x)) {
	//					done[i] = 2;
	//					result.get((x > 0) ? 0 : 1).add(new Literal(intToVar.get(Math.abs(x))));
	//					backbone.push(x);
	//				}
	//			}
	//
	//			for (int j = 0; j < model.length; j++) {
	//				final int y = model[j];
	//				if (done[j] < 2) {
	//					done[j] = 2;
	//					final ArrayList<Literal> setList = new ArrayList<>();
	//					setList.add(new Literal(intToVar.get(Math.abs(y))));
	//
	//					backbone.push(y);
	//					for (int i = 0; i < model.length; i++) {
	//						if (done[i] < 2) {
	//							final int x = model[i];
	//							done[i] = (byte) ((x * y < 0) ? 0 : sat(backbone, -x) ? 0 : 1);
	//						}
	//					}
	//
	//					backbone.pop().push(-y);
	//					for (int i = 0; i < model.length; i++) {
	//						if (done[i] == 1) {
	//							final int x = model[i];
	//							if (!sat(backbone, x)) {
	//								done[i] = 2;
	//								setList.add(new Literal(intToVar.get(Math.abs(x))));
	//							}
	//						}
	//					}
	//					backbone.pop();
	//					result.add(setList);
	//				}
	//			}
	//			return result;
	//		}
	//		return Collections.emptyList();
	//	}
	//
	//	private boolean sat(IVecInt backbone, int x) {
	//		backbone.push(x);
	//		try {
	//			return (solver.isSatisfiable(backbone));
	//		} catch (TimeoutException e) {
	//			FMCorePlugin.getDefault().logError(e);
	//			return false;
	//		} finally {
	//			backbone.pop();
	//		}
	//	}

	//	private List<Literal> convertToNodes(final IVecInt backbone) {
	//		final ArrayList<Literal> list = new ArrayList<Literal>(backbone.size());
	//
	//		final IteratorInt iter = backbone.iterator();
	//		while (iter.hasNext()) {
	//			final int value = iter.next();
	//			list.add(new Literal(intToVar.get(Math.abs(value)), value > 0));
	//		}
	//		return list;
	//	}

	public void setBackbone(List<Literal> knownLiterals) {
		for (int i = 0; i < solvers.length; i++) {
			final Solver solver = solvers[i];
			solver.backbone = new VecInt((knownLiterals.size()) << 1);
			for (Literal node : knownLiterals) {
				solver.backbone.push(getIntOfLiteral(node));
			}
		}
		isSatisfiable();
	}

	public void setBackbone(List<Literal> knownLiterals, Literal curLiteral) {
		final int[] literals = new int[knownLiterals.size() + 1];
		int i = 0;
		for (Literal node : knownLiterals) {
			literals[i++] = getIntOfLiteral(node);
		}
		literals[i] = getIntOfLiteral(curLiteral);
		for (Solver solver : solvers) {
			solver.backbone = newCopiedVecInt(literals, 0);
		}
		isSatisfiable();
	}

	public boolean isSatisfiable() {
		try {
			satisfiable = solvers[0].isSatisfiable();
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		if (satisfiable) {
			model = solvers[0].solver.model();
			//			for (int i = 0; i < model.length; i++) {
			//				b[i] = (byte) Math.signum(model[i]);
			//			}
			//			assert model.length == b.length : "Short Model Length";
		} else {
			throw new RuntimeException("Contradiction");
		}
		return satisfiable;
	}

	public byte getValueOf(Literal literal, int solverIndex) {
		final int i = getIntOfLiteral(literal) - 1;
		return (model[i] != 0) ? getValueOf(i, solverIndex) : 0;
	}

	public boolean isFalse(Literal literal, int solverIndex) {
		final int i = getIntOfLiteral(literal) - 1;
		return (model[i] < 0) && getValueOf(i, solverIndex) != 0;
	}

	public boolean isTrue(Literal literal, int solverIndex) {
		final int i = getIntOfLiteral(literal) - 1;
		return (model[i] > 0) && getValueOf(i, solverIndex) != 0;
	}

	private byte getValueOf(int varIndex, int solverIndex) {
		if (satisfiable) {
			final int x = model[varIndex];
			final Solver solver = solvers[solverIndex];
			solver.backbone.push(-x);
			try {
				if (solver.isSatisfiable()) {
					solver.backbone.pop();
					updateModel(solver.solver.model(), 0);
				} else {
					solver.backbone.pop().push(x);
					return (byte) Math.signum(x);
				}
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
				solver.backbone.pop();
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
