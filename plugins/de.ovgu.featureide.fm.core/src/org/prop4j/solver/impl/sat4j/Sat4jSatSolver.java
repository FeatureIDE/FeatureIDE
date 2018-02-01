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
package org.prop4j.solver.impl.sat4j;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Stack;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solverOld.VarOrderHeap2;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.NegativeLiteralSelectionStrategy;
import org.sat4j.minisat.orders.PositiveLiteralSelectionStrategy;
import org.sat4j.minisat.orders.RSATPhaseSelectionStrategy;
import org.sat4j.minisat.orders.RandomLiteralSelectionStrategy;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.util.RingList;

/**
 * Finds certain solutions of propositional formulas using the Sat4J solver.
 *
 * @author Joshua Sprey
 */
public class Sat4jSatSolver extends AbstractSatSolver {

	public static enum SelectionStrategy {
		NEGATIVE, ORG, POSITIVE, RANDOM
	}

	protected Solver<?> solver;
	protected final int[] order;
	protected final VecInt assignment;
	protected RingList<int[]> solutionList = null;
	protected Stack<Node> pushstack;
	protected ArrayList<IConstr> constrList;

	public static final String CONFIG_TIMEOUT = "Timeout";
	public static final String CONFIG_VERBOSE = "Verbose";
	public static final String CONFIG_DB_SIMPLIFICATION_ALLOWED = "DBSimplification";
	public static final String CONFIG_SELECTION_STRATEGY = "SelectionStrategy";

	public Sat4jSatSolver(ISatProblem problem, Map<String, Object> config) {
		super(problem);

		if (constrList == null) {
			constrList = new ArrayList<>();
		}

		final int numberOfVariables = problem.getNumberOfVariables();
		order = new int[numberOfVariables];
		assignment = new VecInt(numberOfVariables);
		pushstack = new Stack<>();

		// Init Solver with configuration
		solver = initSolver(config);
		try {
			addVariables();
		} catch (final ContradictionException e) {
			FMCorePlugin.getDefault().logError(e);
			throw new RuntimeException();
		}
	}

	protected Solver<?> initSolver(Map<String, Object> config) {
		final Solver<?> solver = (Solver<?>) SolverFactory.newDefault();
		setConfiguration(config);
		return solver;
	}

	@Override
	public void setConfiguration(Map<String, Object> config) {
		for (final String configID : config.keySet()) {
			final Object value = config.get(configID);
			if (value == null) {
				continue;
			}
			switch (configID) {
			case CONFIG_TIMEOUT:
				if (value instanceof Integer) {
					final int timeout = (int) value;
					solver.setTimeoutMs(timeout);
				}
				break;
			case CONFIG_VERBOSE:
				if (value instanceof Boolean) {
					final boolean verbose = (boolean) value;
					solver.setVerbose(verbose);
				}
				break;
			case CONFIG_DB_SIMPLIFICATION_ALLOWED:
				if (value instanceof Boolean) {
					final boolean dbSimpiAllowed = (boolean) value;
					solver.setDBSimplificationAllowed(dbSimpiAllowed);
				}
				break;
			case CONFIG_SELECTION_STRATEGY:
				if (value instanceof SelectionStrategy) {
					final SelectionStrategy strategy = (SelectionStrategy) value;
					switch (strategy) {
					case NEGATIVE:
						solver.setOrder(new VarOrderHeap2(new NegativeLiteralSelectionStrategy(), order));
						break;
					case ORG:
						solver.setOrder(new VarOrderHeap(new RSATPhaseSelectionStrategy()));
						break;
					case POSITIVE:
						solver.setOrder(new VarOrderHeap2(new PositiveLiteralSelectionStrategy(), order));
						break;
					case RANDOM:
						solver.setOrder(new VarOrderHeap2(new RandomLiteralSelectionStrategy(), order));
						break;
					default:
						break;
					}
				}
				break;
			default:
				break;
			}
		}

	}

	private void addVariables() throws ContradictionException {
		final int size = getProblem().getNumberOfVariables();
		if (size > 0) {
			solver.newVar(size);
			solver.setExpectedNumberOfClauses(getProblem().getRoot().getChildren().length + 1);
			addCNF(getProblem().getRoot().getChildren());
			final VecInt pseudoClause = new VecInt(size + 1);
			for (int i = 1; i <= size; i++) {
				pseudoClause.push(i);
			}
			pseudoClause.push(-1);
			solver.addClause(pseudoClause);
		}
		fixOrder();
		solver.getOrder().init();
	}

	public List<IConstr> addClauses(Node constraint) throws ContradictionException {
		return addCNF(constraint.getChildren());
	}

	protected List<IConstr> addCNF(final Node[] cnfChildren) throws ContradictionException {
		final List<IConstr> result = new ArrayList<>(cnfChildren.length);
		for (final Node node : cnfChildren) {
			result.add(addClause(node));
		}
		return result;
	}

	protected IConstr addClause(final Node node) throws ContradictionException {
		final Node[] children = node.getChildren();
		final int[] clause = new int[children.length];
		for (int i = 0; i < children.length; i++) {
			final Literal literal = (Literal) children[i];
			clause[i] = getProblem().getIndexOfVariable(literal);
		}
		return solver.addClause(new VecInt(clause));
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#isSatisfiable()
	 */
	@Override
	public boolean isSatisfiable() {
		try {
			if (solver.isSatisfiable(assignment, false)) {
				if (solutionList != null) {
					solutionList.add(solver.model());
				}
				return true;
			} else {
				return false;
			}
		} catch (final TimeoutException e) {
			e.printStackTrace();
			return false;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#pop()
	 */
	@Override
	public Node pop() {
		if (assignment.isEmpty()) {
			return null;
		}
		final Node oldNode = pushstack.pop();
		if (oldNode instanceof Literal) {
			assignment.pop();
		} else if (oldNode instanceof Or) {
			removeLastClauses(1);
		}
		return oldNode;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#pop(int)
	 */
	@Override
	public List<Node> pop(int count) {
		final ArrayList<Node> nodes = new ArrayList<>();
		for (int i = 0; i < count; i++) {
			nodes.add(pop());
		}
		return nodes;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#push(org.prop4j.Node)
	 */
	@Override
	public void push(Node formula) {
		if (formula instanceof Literal) {
			final Literal literal = (Literal) formula;
			final List<Object> variables = literal.getVariables();
			if (variables.isEmpty()) {
				return;
			}
			final Object variable = variables.get(0);
			assignment.push(getProblem().getIndexOfVariable(variable));
			pushstack.push(formula);
		} else if (formula instanceof Or) {
			try {
				final Node[] children = formula.getChildren();
				final int[] clause = new int[children.length];
				for (int i = 0; i < children.length; i++) {
					final Literal literal = (Literal) children[i];
					clause[i] = getProblem().getIndexOfVariable(literal);
				}
				constrList.add(solver.addClause(new VecInt(clause)));
				pushstack.push(formula);
			} catch (final ContradictionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

		}
	}

	public void removeLastClauses(int numberOfClauses) {
		for (int i = 0; i < numberOfClauses; i++) {
			final IConstr removeLast = constrList.remove(constrList.size() - 1);
			if (removeLast != null) {
				solver.removeSubsumedConstr(removeLast);
			}
		}
		solver.clearLearntClauses();
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#push(org.prop4j.Node[])
	 */
	@Override
	public void push(Node... formulas) {
		for (int i = 0; i < formulas.length; i++) {
			push(formulas[i]);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getSoulution()
	 */
	@Override
	public Object[] getSoulution() {
		final int[] model = solver.model();
		if (model == null) {
			return null;
		}
		final List<Object> objectModel = new ArrayList<Object>();
		objectModel.addAll(Arrays.asList(model));
		return objectModel.toArray();
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#findSolution()
	 */
	@Override
	public Object[] findSolution() {
		if (isSatisfiable() == true) {
			final int[] model = solver.model();
			final List<Object> objectModel = new ArrayList<Object>();
			objectModel.addAll(Arrays.asList(model));
			return objectModel.toArray();
		}
		return null;
	}

	public void setOrder(List<IFeature> orderList) {
		int i = -1;
		for (final IFeature feature : orderList) {
			order[++i] = getProblem().getIndexOfVariable(feature.getName());
		}
	}

	public int[] getOrder() {
		return order;
	}

	public void shuffleOrder() {
		final Random rnd = new Random();
		for (int i = order.length - 1; i >= 0; i--) {
			final int index = rnd.nextInt(i + 1);
			final int a = order[index];
			order[index] = order[i];
			order[i] = a;
		}
	}

	public void fixOrder() {
		for (int i = 0; i < order.length; i++) {
			order[i] = i + 1;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		final String cnf = getProblem().getRoot().toString();
		String pushed = "";
		for (final Node node : pushstack) {
			pushed += node.toString() + "\n";
		}

		return cnf + "\n\nPushed:\n" + pushed;
	}
}
