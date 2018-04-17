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

import static de.ovgu.featureide.fm.core.localization.StringTable.EXPRESSION_IS_NOT_IN_CNF;
import static de.ovgu.featureide.fm.core.localization.StringTable.ONLY;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.sat4j.core.ConstrGroup;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.NegativeLiteralSelectionStrategy;
import org.sat4j.minisat.orders.PositiveLiteralSelectionStrategy;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;
import org.sat4j.tools.SolutionCounter;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * A solver that computes if a given propositional node is satisfiable and retrieves solutions.
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
		this(node, timeout, true);
	}

	public SatSolver(Node node, long timeout, boolean createCNF) {
		varToInt = new HashMap<Object, Integer>();
		intToVar = new HashMap<Integer, Object>();
		readVars(node);

		initSolver(node, timeout, createCNF);
	}

	protected void readVars(Node node) {
		if (node instanceof Literal) {
			final Object var = ((Literal) node).var;
			if (!varToInt.containsKey(var)) {
				final int index = varToInt.size() + 1;
				varToInt.put(var, index);
				intToVar.put(index, var);
			}
		} else {
			for (final Node child : node.getChildren()) {
				readVars(child);
			}
		}
	}

	protected void initSolver(Node node, long timeout, boolean createCNF) {
		solver = SolverFactory.newDefault();
		solver.setTimeoutMs(timeout);
		solver.newVar(varToInt.size());

		addClauses(createCNF ? node.toCNF() : node.clone());
	}

	public void setTimeout(long timeout) {
		solver.setTimeoutMs(timeout);
	}

	/**
	 * Adds clauses to the SatSolver. Assumes that the given node is in CNF.
	 *
	 * @param root the new clauses (e.g. AND or OR node)
	 */
	public void addClauses(Node root) {
		if (contradiction) {
			return;
		}
		try {
			if (root instanceof And) {
				for (final Node node : root.getChildren()) {
					addClause(node);
				}
			} else {
				addClause(root);
			}
		} catch (final ContradictionException e) {
			contradiction = true;
		}
	}

	protected IConstr addClause(Node node) throws ContradictionException {
		try {
			if (node instanceof Or) {
				final int[] clause = new int[node.children.length];
				int i = 0;
				for (final Node child : node.getChildren()) {
					clause[i++] = getIntOfLiteral(child);
				}
				return solver.addClause(new VecInt(clause));
			} else {
				final int literal = getIntOfLiteral(node);
				return solver.addClause(new VecInt(new int[] { literal }));
			}
		} catch (final ClassCastException e) {
			throw new RuntimeException(EXPRESSION_IS_NOT_IN_CNF, e);
		}
	}

	protected int getIntOfLiteral(Node node) {
		final Object var = ((Literal) node).var;
		if (!varToInt.containsKey(var)) {
			final int index = varToInt.size() + 1;
			varToInt.put(var, index);
			intToVar.put(index, var);
			solver.newVar(1);
			// hack to get around an ArrayIndexOutOfBoundsException by Sat4J
			// 2.0.5
			try {
				solver.addClause(new VecInt(new int[] { index, -index }));
			} catch (final ContradictionException e) {
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
		} catch (final TimeoutException e) {
			Logger.logError(e);
			return false;
		}
		return !contradiction;
	}

	public List<Literal> knownValues(Literal... tempNodes) {
		return knownValues(ValueType.ALL, tempNodes);
	}

	public List<Literal> knownValues(ValueType vt, Literal... tempNodes) {
		if (test()) {
			final IVecInt backbone = new VecInt();
			for (int i = 0; i < tempNodes.length; i++) {
				backbone.push(getIntOfLiteral(tempNodes[i]));
			}

			final int[] model = solver.model();
			for (int i = 0; i < model.length; i++) {
				final int x = model[i];
				if ((x * vt.factor) >= 0) {
					backbone.push(-x);
					try {
						if (solver.isSatisfiable(backbone)) {
							backbone.pop();
						} else {
							backbone.pop().push(x);
						}
					} catch (final TimeoutException e) {
						Logger.logError(e);
						backbone.pop();
					}
				}
			}

			for (int i = 0; i < tempNodes.length; i++) {
				backbone.delete(i);
			}
			return convertToNodes(backbone);
		}
		return Collections.emptyList();
	}

	public void setDBSimplificationAllowed(boolean allowed) {
		solver.setDBSimplificationAllowed(allowed);
	}

	public void removeConstraint(IConstr constr) {
		solver.removeConstr(constr);
	}

	public List<IConstr> addTempConstraint(Node constraint) {
		final List<IConstr> result = new LinkedList<>();
		try {
			if (constraint instanceof And) {
				for (final Node node : constraint.getChildren()) {
					result.add(addClause(node));
				}
			} else {
				result.add(addClause(constraint));
			}
		} catch (final ContradictionException e) {
			contradiction = true;
		}
		return result;
	}

	public boolean isImplied(Literal... or) {
		if (!contradiction) {
			final IVecInt backbone = new VecInt();
			for (int i = 0; i < or.length; i++) {
				final Literal node = or[i];
				backbone.push(node.positive ? -varToInt.get(node.var) : varToInt.get(node.var));
			}
			try {
				return !solver.isSatisfiable(backbone);
			} catch (final TimeoutException e) {
				Logger.logError(e);
			}
		}
		return false;
	}

	public boolean isImplied(Node[] or) {
		return isImplied(Arrays.copyOf(or, or.length, Literal[].class));
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
							done[i] = (byte) (((x * y) < 0) ? 0 : sat(backbone, -x) ? 0 : 1);
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

	public List<List<Literal>> atomicSuperSets() {
		if (test()) {
			final int[] globalModel = solver.model();
			final byte[] done = new byte[globalModel.length];
			max = solver.nVars();

			return atomicSuperSets(globalModel, done);
		}
		return Collections.emptyList();
	}

	public List<List<Literal>> atomicSuperSets(Collection<String> featureSet) {
		if (test()) {
			final int[] globalModel = solver.model();
			final byte[] done = new byte[globalModel.length];
			max = 0;

			Arrays.fill(done, (byte) 2);
			for (final String b : featureSet) {
				final Integer x = varToInt.get(b);
				if (x != null) {
					done[x - 1] = 0;
					max++;
				} else {
					throw new RuntimeException("Unkown Feature " + b);
				}
			}

			return atomicSuperSets(globalModel, done);
		}
		return Collections.emptyList();
	}

	private int max = 0;

	private List<List<Literal>> atomicSuperSets(final int[] globalModel, final byte[] done) {
		final List<List<Literal>> result = new ArrayList<>();
		final ArrayList<Literal> coreList = new ArrayList<>();
		result.add(coreList);

		final IVecInt backbone = new VecInt();

		int c = 0;
		for (int i = 0; i < globalModel.length; i++) {
			final int x = globalModel[i];
			if (done[i] == 0) {
				done[i] = 2;
				System.out.println("\t\t" + ++c + " / " + max);

				if (!sat(backbone, -x)) {
					backbone.push(x);
					coreList.add(new Literal(intToVar.get(Math.abs(x)), x > 0));
				} else {
					final ArrayList<Literal> setList = new ArrayList<>();
					setList.add(new Literal(intToVar.get(Math.abs(x)), x > 0));

					final int[] model = solver.model();
					backbone.push(-x);

					for (int j = i + 1; j < model.length; j++) {
						if (done[j] == 0) {
							final int y = model[j];

							if (!sat(backbone, -y)) {
								done[j] = 1;
							}
						}
					}

					backbone.pop().push(x);
					for (int j = i + 1; j < model.length; j++) {
						if (done[j] == 1) {
							final int y = model[j];

							if (!sat(backbone, y)) {
								done[j] = 2;
								setList.add(new Literal(intToVar.get(Math.abs(y)), y > 0));
								System.out.println("\t\t" + ++c + " / " + max);
							} else {
								done[j] = 0;
							}
						}
					}
					backbone.pop();
					result.add(setList);
				}
			}
		}
		return result;
	}

	private boolean sat(IVecInt backbone, int x) {
		backbone.push(x);
		try {
			return (solver.isSatisfiable(backbone, false));
		} catch (final TimeoutException e) {
			Logger.logError(e);
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
	 * Where f is the formula currently feed into the solver and l1,...,ln are the elements in the given array <code>literals</code>.
	 *
	 * @param literals an array of literals for which the value is assumed
	 * @return true if the formula with all assumed values is satisfiable
	 * @throws TimeoutException
	 */
	public boolean isSatisfiable(Node[] literals) throws TimeoutException {
		if (contradiction) {
			return false;
		}
		final int[] unitClauses = new int[literals.length];
		int i = 0;
		for (final Node literal : literals) {
			unitClauses[i++] = getIntOfLiteral(literal);
		}
		return solver.isSatisfiable(new VecInt(unitClauses));
	}

	/**
	 * Checks whether the formula the following formula is satisfiable.
	 *
	 * f and l1 and l2 and ... and ln
	 *
	 * Where f is the formula currently feed into the solver and l1,...,ln are the elements in the given list <code>literals</code>.
	 *
	 * @param literals a list of literals for which the value is assumed
	 * @return true if the formula with all assumed values is satisfiable
	 * @throws TimeoutException
	 */
	public boolean isSatisfiable(List<Node> literals) throws TimeoutException {
		if (contradiction) {
			return false;
		}
		final int[] unitClauses = new int[literals.size()];
		int i = 0;
		for (final Node literal : literals) {
			unitClauses[i++] = getIntOfLiteral(literal);
		}
		return solver.isSatisfiable(new VecInt(unitClauses));
	}

	/**
	 * Checks whether the formula the following formula is satisfiable.
	 *
	 * f and g
	 *
	 * Where f is the formula currently feed into the solver and g is the formula given in the parameter <code>node</code>.
	 *
	 * @param node a propositional formula
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

		final ConstrGroup group = new ConstrGroup();
		try {
			final IVecInt unit = new VecInt();
			for (final Node child : node.getChildren()) {
				if (child instanceof Or) {
					final IVecInt clause = new VecInt();
					for (final Node literal : child.getChildren()) {
						clause.push(getIntOfLiteral(literal));
					}
					group.add(solver.addClause(clause));
				} else {
					unit.push(getIntOfLiteral(child));
				}
			}
			return solver.isSatisfiable(unit);
		} catch (final ContradictionException e) {
			return false;
		} finally {
			group.removeFrom(solver);
		}
	}

	/**
	 * Counts the solutions of the propositional formula. If the given timeout is reached the result is negative.
	 *
	 * Since -0 equals 0, the output is y = -1 - x. If the output y is negative there are at least x = -1 - y solutions.
	 *
	 * @return number of solutions (at least solutions)
	 */
	public long countSolutions() {
		if (contradiction) {
			return 0;
		}
		long number = 0;
		final SolutionCounter counter = new SolutionCounter(solver);

		try {
			number = counter.countSolutions();
		} catch (final TimeoutException e) {
			number = -1 - counter.lowerBound();
		}
		return number;
	}

	public long countSolutions(Literal[] literals) {
		long number = 0;
		if (!contradiction) {
			final ReusableModelIterator it = new ReusableModelIterator(solver);
			solver.expireTimeout();
			if ((literals != null) && (literals.length > 0)) {
				final int[] unitClauses = new int[literals.length];
				for (int i = 0; i < literals.length; i++) {
					unitClauses[i] = getIntOfLiteral(literals[i]);
				}
				it.setAssumptions(new VecInt(unitClauses));
			}
			number = it.count();
		}
		return number;
	}

	public String getSolutions(int number) throws TimeoutException {
		if (contradiction) {
			return "contradiction\n";
		}

		final StringBuilder out = new StringBuilder();
		final IProblem problem = new ModelIterator(solver);
		int[] lastModel = null;
		for (int i = 0; i < number; i++) {
			if (!problem.isSatisfiable(i > 0)) {
				out.append(ONLY + i + " solutions\n");
				break;
			}
			final int[] model = problem.model();
			if (lastModel != null) {
				boolean same = true;
				for (int j = 0; j < model.length; j++) {
					if (model[j] != lastModel[j]) {
						same = false;
					}
				}
				if (same) {
					out.append(ONLY + i + " solutions\n");
					break;
				}
			}
			lastModel = model;
			final StringBuilder pos = new StringBuilder();
			final StringBuilder neg = new StringBuilder();
			for (final int var : model) {
				if (var > 0) {
					pos.append(intToVar.get(Math.abs(var)) + " ");
				} else {
					neg.append(intToVar.get(Math.abs(var)) + " ");
				}
			}
			out.append("true: " + pos + "    false: " + neg + "\n");
		}
		return out.toString();
	}

	public LinkedList<List<String>> getSolutionFeatures(Literal[] literals, int number) throws TimeoutException {
		final LinkedList<List<String>> solutionList = new LinkedList<List<String>>();

		if (!contradiction) {
			final int[] unitClauses = new int[literals.length];
			for (int i = 0; i < literals.length; i++) {
				unitClauses[i] = getIntOfLiteral(literals[i]);
			}
			final VecInt assumps = new VecInt(unitClauses);

			final ModelIterator modelIterator = new ModelIterator(solver, number);
			while (modelIterator.isSatisfiable(assumps)) {
				final int[] model = modelIterator.model();

				final List<String> featureList = new LinkedList<>();
				for (final int var : model) {
					if (var > 0) {
						featureList.add(intToVar.get(Math.abs(var)).toString());
					}
				}
				solutionList.add(featureList);
			}
		}

		return solutionList;
	}

	public LinkedList<List<String>> getSolutionFeatures(int number) throws TimeoutException {
		final LinkedList<List<String>> solutionList = new LinkedList<List<String>>();

		if (!contradiction) {
			final IProblem problem = new ModelIterator(solver);
			int[] lastModel = null;
			for (int i = 0; i < number; i++) {
				final List<String> featureList = new LinkedList<String>();

				if (!problem.isSatisfiable(i > 0)) {
					break;
				}

				final int[] model = problem.model();
				if (lastModel != null) {
					boolean same = true;
					for (int j = 0; j < model.length; j++) {
						if (model[j] != lastModel[j]) {
							same = false;
						}
					}
					if (same) {
						break;
					}
				}

				lastModel = model;

				for (final int var : model) {
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

		final StringBuilder out = new StringBuilder();
		final IProblem problem = new ModelIterator(solver);
		if (!problem.isSatisfiable()) {
			return null;
		}
		final int[] model = problem.model();
		for (final int var : model) {
			if (var > 0) {
				out.append(intToVar.get(Math.abs(var)) + "\n");
			}
		}
		return out.toString();
	}

	public List<String> getSolution(boolean positive) {
		if (!contradiction) {
			final Solver<?> s = ((Solver<?>) solver);
			final IOrder oldOrder = s.getOrder();

			try {
				s.setOrder(new VarOrderHeap(positive ? new PositiveLiteralSelectionStrategy() : new NegativeLiteralSelectionStrategy()));

				final int[] model = solver.findModel();
				if (model != null) {
					final List<String> resultList = new ArrayList<>();
					for (final int var : model) {
						final Object varObject = intToVar.get(var);
						if (varObject instanceof String) {
							resultList.add((String) varObject);
						}
					}

					return resultList;
				}
			} catch (final Exception e) {
				Logger.logError(e);
			} finally {
				s.setOrder(oldOrder);
			}

		}
		return Collections.emptyList();
	}

	public void reset() {
		solver.reset();
	}

	/**
	 * Creates one solutions to cover the given features.
	 *
	 * @param features The features that should be covered.
	 * @param selection true is the features should be selected, false otherwise.
	 */
	public List<String> coverFeatures(Collection<String> features, boolean selection, IMonitor monitor) throws TimeoutException {
		final VecInt vector = new VecInt();
		final List<String> coveredFeatures = new LinkedList<>();
		for (final String feature : features) {
			final Integer integer = (selection ? 1 : -1) * varToInt.get(feature);
			vector.push(integer);
			if (solver.isSatisfiable(vector)) {
				monitor.worked();
				coveredFeatures.add(feature);
			} else {
				vector.pop().push(-integer);
			}
		}
		features.removeAll(coveredFeatures);
		if (coveredFeatures.isEmpty()) {
			throw new RuntimeException("Something went wrong! No features are covered.");
		}
		if (!solver.isSatisfiable(vector)) {
			throw new RuntimeException("Unexpected solver exception");
		}

		final int[] model = solver.model();
		final List<String> featureList = new ArrayList<String>(model.length);
		for (final int var : model) {
			if (var > 0) {
				featureList.add(intToVar.get(var).toString().intern());
			}
		}

		return featureList;
	}

}
