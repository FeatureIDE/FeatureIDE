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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;
import org.sat4j.tools.SolutionCounter;

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * A solver that computes if a given propositional node is satisfiable and
 * retrieves solutions.
 * 
 * @author Thomas Thuem
 */
public class SatSolver {
	
	public static enum ValueType {
		ALL(0), TRUE(1), FALSE(-1);
		
		private final int factor;

		private ValueType(int factor) {
			this.factor = factor;
		}
		
	}

	protected boolean contradiction = false;

	protected HashMap<Object, Integer> varToInt;

	protected HashMap<Integer, Object> intToVar;

	protected ISolver solver;

	public SatSolver(Node node, long timeout) {
		varToInt = new HashMap<Object, Integer>();
		intToVar = new HashMap<Integer, Object>();
		readVars(node);

		initSolver(node, timeout);
	}

	protected void readVars(Node node) {
		if (node instanceof Literal) {
			Object var = ((Literal) node).var;
			if (!varToInt.containsKey(var)) {
				int index = varToInt.size() + 1;
				varToInt.put(var, index);
				intToVar.put(index, var);
			}
		} else
			for (Node child : node.getChildren())
				readVars(child);
	}

	protected void initSolver(Node node, long timeout) {
		solver = SolverFactory.newDefault();
		solver.setTimeoutMs(timeout);
		node = node.toCNF();
		solver.newVar(varToInt.size());
		addClauses(node);
	}
	
	public void setTimeout(long timeout) {
		solver.setTimeoutMs(timeout);
	}
	
	/**
	 * Adds clauses to the SatSolver. Assumes that the given node is in CNF.
	 * 
	 * @param root 
	 * 		the new clauses (e.g. AND or OR node)
	 */
	public void addClauses(Node root) {
		if (contradiction) {
			return;
		}
		try {
			if (root instanceof And) {
				for (Node node : root.getChildren()) {
					addClause(node);
				}
			} else {
				addClause(root);
			}
		} catch (ContradictionException e) {
			contradiction = true;
		}
	}

	protected void addClause(Node node) throws ContradictionException {
		try {
			if (node instanceof Or) {
				int[] clause = new int[node.children.length];
				int i = 0;
				for (Node child : node.getChildren()) {
					clause[i++] = getIntOfLiteral(child);
				}
				solver.addClause(new VecInt(clause));
			} else {
				int literal = getIntOfLiteral(node);
				solver.addClause(new VecInt(new int[] { literal }));
			}
		} catch (ClassCastException e) {
			throw new RuntimeException("expression is not in cnf", e);
		}
	}

	protected int getIntOfLiteral(Node node) {
		Object var = ((Literal) node).var;
		if (!varToInt.containsKey(var)) {
			int index = varToInt.size() + 1;
			varToInt.put(var, index);
			intToVar.put(index, var);
			solver.newVar(1);
			// hack to get around an ArrayIndexOutOfBoundsException by Sat4J
			// 2.0.5
			try {
				solver.addClause(new VecInt(new int[] { index, -index }));
			} catch (ContradictionException e) {
				// cannot occur
			}
			// hack end
		}
		int value = varToInt.get(var);
		value *= ((Literal) node).positive ? 1 : -1;
		return value;
	}
	
	private boolean test() {
		try {
			contradiction = contradiction || !solver.isSatisfiable();
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
			return false;
		}
		return !contradiction;
	}
	
	public List<Literal> knownValues(Literal... tempNodes) {
		return knownValues(ValueType.ALL, tempNodes);
	}
	
	public List<Literal> knownValues(ValueType vt, Literal... tempNodes) {
		if (!contradiction) {
			final IVecInt backbone = new VecInt();
			for (int i = 0; i < tempNodes.length; i++) {
				backbone.push(getIntOfLiteral(tempNodes[i]));
			}

			boolean satisfiable = false;
			try {
				satisfiable = solver.isSatisfiable(backbone);
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
			}
			if (satisfiable) {
				final byte[] b = new byte[solver.nVars()];
				final int[] model = solver.model();
				for (int i = 0; i < model.length; i++) {
					b[i] = (byte) Math.signum(model[i]);
				}
				for (int i = 0; i < model.length; i++) {
					if (b[i] == 0) {
						continue;
					}
					final int x = model[i];
					if ((x * vt.factor) >= 0) {
						backbone.push(-x);
						try {
							if (solver.isSatisfiable(backbone)) {
								backbone.pop();
								final int[] tempModel = solver.model();
								for (int j = i + 1; j < tempModel.length; j++) {
									if (b[j] != (byte) Math.signum(tempModel[j])) {
										b[j] = 0;
									}
								}
							} else {
								backbone.pop().push(x);
							}
						} catch (TimeoutException e) {
							FMCorePlugin.getDefault().logError(e);
							backbone.pop();
						}
					}
				}
				
				for (int i = 0; i < tempNodes.length; i++) {
					backbone.delete(i);
				}
				return convertToNodes(backbone);
			}
		}
		return Collections.emptyList();
	}

	public List<List<Literal>> atomicSets() {
		if (test()) {
			final List<List<Literal>> result = new ArrayList<>();
			result.add(new ArrayList<Literal>());
			result.add(new ArrayList<Literal>());

			final IVecInt backbone = new VecInt();
			final int[] model = solver.model();
			final byte[] done = new byte[model.length];

			for (int i = 0; i < model.length; i++) {
				final int x = model[i];
				if (!sat(backbone, -x)) {
					done[i] = 2;
					result.get((x > 0) ? 0 : 1).add(new Literal(intToVar.get(Math.abs(x))));
					backbone.push(x);
				}
			}

			for (int j = 0; j < model.length; j++) {
				final int y = model[j];
				if (done[j] < 2) {
					done[j] = 2;
					final ArrayList<Literal> setList = new ArrayList<>();
					setList.add(new Literal(intToVar.get(Math.abs(y))));
					
					backbone.push(y);
					for (int i = 0; i < model.length; i++) {
						if (done[i] < 2) {
							final int x = model[i];
							done[i] = (byte) ((x * y < 0) ? 0 : sat(backbone, -x) ? 0 : 1);
						}
					}

					backbone.pop().push(-y);
					for (int i = 0; i < model.length; i++) {
						if (done[i] == 1) {
							final int x = model[i];
							if (!sat(backbone, x)) {
								done[i] = 2;
								setList.add(new Literal(intToVar.get(Math.abs(x))));
							}
						}
					}
					backbone.pop();
					result.add(setList);
				}
			}
			return result;
		}
		return Collections.emptyList();
	}

	private boolean sat(IVecInt backbone, int x) {
		backbone.push(x);
		try {
			return (solver.isSatisfiable(backbone));
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
			return false;
		} finally {
			backbone.pop();
		}
	}

	private List<Literal> convertToNodes(final IVecInt backbone) {
		final ArrayList<Literal> list = new ArrayList<Literal>(backbone.size());
		
		final IteratorInt iter = backbone.iterator();
		while (iter.hasNext()) {
			final int value = iter.next();
			list.add(new Literal(intToVar.get(Math.abs(value)), value > 0));
		}
		return list;
	}

	/**
	 * Checks whether the formula currently feed into the solver is satisfiable.
	 * 
	 * @return true if the formula is satisfiable
	 * @throws TimeoutException
	 */
	public boolean isSatisfiable() throws TimeoutException {
		return !contradiction && solver.isSatisfiable();
	}

	/**
	 * Checks whether the formula the following formula is satisfiable.
	 * 
	 * f and l1 and l2 and ... and ln
	 * 
	 * Where f is the formula currently feed into the solver and l1,...,ln are
	 * the elements in the given array <code>literals</code>.
	 * 
	 * @param literals
	 *            an array of literals for which the value is assumed
	 * @return true if the formula with all assumed values is satisfiable
	 * @throws TimeoutException
	 */
	public boolean isSatisfiable(Node[] literals) throws TimeoutException {
		if (contradiction)
			return false;
		int[] unitClauses = new int[literals.length];
		int i = 0;
		for (Node literal : literals)
			unitClauses[i++] = getIntOfLiteral(literal);
		return solver.isSatisfiable(new VecInt(unitClauses));
	}

	/**
	 * Checks whether the formula the following formula is satisfiable.
	 * 
	 * f and l1 and l2 and ... and ln
	 * 
	 * Where f is the formula currently feed into the solver and l1,...,ln are
	 * the elements in the given list <code>literals</code>.
	 * 
	 * @param literals
	 *            a list of literals for which the value is assumed
	 * @return true if the formula with all assumed values is satisfiable
	 * @throws TimeoutException
	 */
	public boolean isSatisfiable(List<Node> literals) throws TimeoutException {
		if (contradiction)
			return false;
		int[] unitClauses = new int[literals.size()];
		int i = 0;
		for (Node literal : literals) {
			unitClauses[i++] = getIntOfLiteral(literal);
		}
		return solver.isSatisfiable(new VecInt(unitClauses));
	}

	/**
	 * Checks whether the formula the following formula is satisfiable.
	 * 
	 * f and g
	 * 
	 * Where f is the formula currently feed into the solver and g is the
	 * formula given in the parameter <code>node</code>.
	 * 
	 * @param node
	 *            a propositional formula
	 * @return true if adding the given formula results in a satisfiable formula
	 * @throws TimeoutException
	 */
	public boolean isSatisfiable(Node node) throws TimeoutException {
		if (contradiction) {
			return false;
		}

		if (!(node instanceof And)) {
			node = new And(node);
		}

		ConstrGroup group = new ConstrGroup();
		IVecInt unit = new VecInt();
		try {
			for (Node child : node.getChildren()) {
				if (child instanceof Or) {
					IVecInt clause = new VecInt();
					for (Node literal : child.getChildren())
						clause.push(getIntOfLiteral(literal));
					group.add(solver.addClause(clause));
				} else {
					unit.push(getIntOfLiteral(child));
				}
			}
		} catch (ContradictionException e) {
			group.removeFrom(solver);
			return false;
		}

		boolean satisfiable = solver.isSatisfiable(unit);
		group.removeFrom(solver);
		return satisfiable;
	}

	/**
	 * Counts the solutions of the propositional formula. If the given timeout
	 * is reached the result is negative.
	 * 
	 * Since -0 equals 0, the output is y = -1 - x. If the output y is negative
	 * there are at least x = -1 - y solutions.
	 * 
	 * @return number of solutions (at least solutions)
	 */
	public long countSolutions() {
		if (contradiction)
			return 0;
		long number = 0;
		SolutionCounter counter = new SolutionCounter(solver);
		try {
			number = counter.countSolutions();
		} catch (TimeoutException e) {
			number = -1 - counter.lowerBound();
		}
		return number;
	}

	public String getSolutions(int number) throws TimeoutException {
		if (contradiction)
			return "contradiction\n";

		StringBuilder out = new StringBuilder();
		IProblem problem = new ModelIterator(solver);
		int[] lastModel = null;
		for (int i = 0; i < number; i++) {
			if (!problem.isSatisfiable(i > 0)) {
				out.append("only " + i + " solutions\n");
				break;
			}
			int[] model = problem.model();
			if (lastModel != null) {
				boolean same = true;
				for (int j = 0; j < model.length; j++)
					if (model[j] != lastModel[j])
						same = false;
				if (same) {
					out.append("only " + i + " solutions\n");
					break;
				}
			}
			lastModel = model;
			StringBuilder pos = new StringBuilder();
			StringBuilder neg = new StringBuilder();
			for (int var : model)
				if (var > 0)
					pos.append(intToVar.get(Math.abs(var)) + " ");
				else
					neg.append(intToVar.get(Math.abs(var)) + " ");
			out.append("true: " + pos + "    false: " + neg + "\n");
		}
		return out.toString();
	}

	public LinkedList<List<String>> getSolutionFeatures(int number)
			throws TimeoutException {
		final LinkedList<List<String>> solutionList = new LinkedList<List<String>>();

		if (!contradiction) {
			IProblem problem = new ModelIterator(solver);
			int[] lastModel = null;
			for (int i = 0; i < number; i++) {
				List<String> featureList = new LinkedList<String>();

				if (!problem.isSatisfiable(i > 0)) {
					break;
				}

				int[] model = problem.model();
				if (lastModel != null) {
					boolean same = true;
					for (int j = 0; j < model.length; j++)
						if (model[j] != lastModel[j])
							same = false;
					if (same) {
						break;
					}
				}

				lastModel = model;

				for (int var : model) {
					if (var > 0) {
						featureList.add(intToVar.get(Math.abs(var)).toString());
					}
				}
				solutionList.add(featureList);
			}
		}

		return solutionList;
	}

	public String getSolution() throws TimeoutException {
		if (contradiction) {
			return null;

		}
		StringBuilder out = new StringBuilder();
		IProblem problem = new ModelIterator(solver);
		if (!problem.isSatisfiable())
			return null;
		int[] model = problem.model();
		for (int var : model) {
			if (var > 0) {
				out.append(intToVar.get(Math.abs(var)) + "\n");
			}
		}
		return out.toString();
	}
}
