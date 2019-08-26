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
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Random;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatResult;
import org.prop4j.solver.impl.SolverUtils;
import org.prop4j.solvers.impl.javasmt.SolverMemory;
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
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.analysis.cnf.solver.VarOrderHeap2;

/**
 *
 * @author Joshua Sprey
 */
public class Sat4jSatSolver extends AbstractSatSolver {

	/** The actually solver instance from Sat4J to solve the problem. */
	protected ISolver solver;
	/** The order of the literals */
	protected final int[] order;
	/** The current vector that holds all assumptions. */
	protected final VecInt assignment = new VecInt();
	/** Hold information about pushed nodes which can be clauses or assumptions. */
	protected LinkedList<Node> pushstack = new LinkedList<>();
	/** the pseudo clause. */
	protected IConstr pseudoClause;
	/**
	 * Holds information about all pushed clauses and the ability to retrieve their index. Keep in mind that the indexes need to be subtracted by 1 (2) because
	 * Sat4J only supports index from 1 (and that the first added clause is a pseudo clause which is always true.)
	 */
	protected SolverMemory<IConstr> memory;

	public Sat4jSatSolver(ISatProblem problem, Map<String, Object> config) throws org.prop4j.solver.ContradictionException {
		super(problem);

		// Init Solver with configuration
		solver = createSolver();
		solver.setTimeoutMs(1000);
		solver.setDBSimplificationAllowed(true);
		solver.setVerbose(false);
		setConfiguration(config);

		if (problem != null) {
			final int numberOfVariables = problem.getNumberOfVariables();
			order = new int[numberOfVariables];
			fixOrder();

			// create the variables for Sat4J
			registerVariables();
		} else {
			order = new int[0];
		}

	}

	public Sat4jSatSolver(ISatProblem problem) throws org.prop4j.solver.ContradictionException {
		super(problem);

		// Init Solver with configuration
		solver = createSolver();
		solver.setTimeoutMs(1000);
		solver.setDBSimplificationAllowed(true);
		solver.setVerbose(false);

		if (problem != null) {
			final int numberOfVariables = problem.getNumberOfVariables();
			order = new int[numberOfVariables];
			fixOrder();

			// create the variables for Sat4J
			registerVariables();
		} else {
			order = new int[0];
		}
	}

	protected ISolver getSolver() {
		if (solver == null) {
			return createSolver();
		}
		return solver;
	}

	protected ISolver createSolver() {
		return SolverFactory.newDefault();
	}

	/**
	 * Adds the variables from the {@link ISatProblem} to the Sat4j solver. Also class the registration for the clauses.
	 */
	private void registerVariables() throws org.prop4j.solver.ContradictionException {
		try {
			final int numberOfVariables = getProblem().getNumberOfVariables();
			if (numberOfVariables > 0) {
				solver.newVar(numberOfVariables);
				// Plus one because the index 0 is not available for Sat4J
				solver.setExpectedNumberOfClauses(getProblem().getClauses().length + 1);

				// Register all clauses from the problem to the solver
				registerClauses(numberOfVariables);
			}
			fixOrder();
			if (solver instanceof Solver<?>) {
				((Solver<?>) solver).getOrder().init();
			}
		} catch (final ContradictionException e) {
			throw new org.prop4j.solver.ContradictionException();
		}
	}

	/**
	 * Adds the clauses from the {@link ISatProblem} to the Sat4j solver.
	 */
	private void registerClauses(int numberOfVariables) throws ContradictionException {
		// Add pseudo clause which is a tautology and contains every variables. Is needed because Sat4J ignores all variables that are not part of any
		// clause. That behavior is not wanted. Start at 1 because 0 is not a valid Sat4j index.
//		final VecInt pseudoClause = new VecInt(numberOfVariables + 1);
//		for (int i = 1; i <= numberOfVariables; i++) {
//			pseudoClause.push(i);
//		}
//		pseudoClause.push(-1);
//		this.pseudoClause = solver.addClause(pseudoClause);

		final List<IConstr> clauses = new ArrayList<>();
		for (final Node node : getProblem().getClauses()) {
			final Node[] children = node.getChildren();
			final int[] clause = new int[children.length];
			for (int i = 0; i < children.length; i++) {
				final Literal literal = (Literal) children[i];
				clause[i] = getProblem().getSignedIndexOfVariable(literal);
			}
			clauses.add(solver.addClause(new VecInt(clause)));
		}
		memory = new SolverMemory<>(getProblem(), clauses);
	}

	/**
	 * Returns the order of the variables used by Sat4J.
	 *
	 * @return Order as array.
	 */
	public int[] getOrder() {
		return order;
	}

	/**
	 * Randomizes the current order.
	 */
	public void shuffleOrder() {
		final Random rnd = new Random();
		for (int i = order.length - 1; i >= 0; i--) {
			final int index = rnd.nextInt(i + 1);
			final int a = order[index];
			order[index] = order[i];
			order[i] = a;
		}
	}

	/**
	 * Fixes the order.
	 */
	public void fixOrder() {
		for (int i = 0; i < order.length; i++) {
			order[i] = i + 1;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#isSatisfiable()
	 */
	@Override
	public ISatResult isSatisfiable() {
		try {
			if (solver.isSatisfiable(assignment)) {
				return ISatResult.TRUE;
			} else {
				return ISatResult.FALSE;
			}
		} catch (final TimeoutException e) {
			return ISatResult.TIMEOUT;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#pop()
	 */
	@Override
	public Node pop() {
		if (pushstack.isEmpty()) {
			return null;
		}
		final Node oldNode = pushstack.pop();
		if (oldNode instanceof Literal) {
			assignment.pop();
		} else if (oldNode instanceof Or) {
			final Node[] children = oldNode.getChildren();
			// Or with only one literal, just add the literal as assumption
			if ((children.length == 1) && (children[0] instanceof Literal)) {
				assignment.pop();
			} else {
				final IConstr constraint = memory.popFormula();
				if (constraint != null) {
					try {
						solver.removeConstr(constraint);
					} catch (final NoSuchElementException e) {}
				}
			}
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
	 * @see org.prop4j.solver.ISolver#pop(int)
	 */
	@Override
	public List<Node> popAll() {
		final ArrayList<Node> nodes = new ArrayList<>();
		final int pushstackLength = pushstack.size();
		for (int i = 0; i < pushstackLength; i++) {
			nodes.add(pop());
		}
		return nodes;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#push(org.prop4j.Node)
	 */
	@Override
	public int push(Node formula) throws org.prop4j.solver.ContradictionException {
		if (formula instanceof Literal) {
			final Literal literal = (Literal) formula;
			assignment.push(getProblem().getSignedIndexOfVariable(literal));
			pushstack.push(formula);
			return 0;
		}
		formula = formula.toCNF();
		if (formula instanceof And) {
			if (formula.getChildren().length > 1) {
				return 0;
			}
			formula = formula.getChildren()[0];
		}
		if (formula instanceof Or) {
			try {
				final Node[] children = formula.getChildren();
				// Or with only one literal, just add the literal as assumption
				if ((children.length == 1) && (children[0] instanceof Literal)) {
					final Literal literal = (Literal) children[0];
					assignment.push(getProblem().getSignedIndexOfVariable(literal));
					pushstack.push(formula);
					return 0;
				}
				final int[] clause = new int[children.length];
				for (int i = 0; i < children.length; i++) {
					final Literal literal = (Literal) children[i];
					clause[i] = getProblem().getSignedIndexOfVariable(literal);
				}
				final IConstr constaint = solver.addClause(new VecInt(clause));
				memory.push(formula, constaint);
				pushstack.push(formula);
				if (constaint != null) {
					return 1;
				} else {
					return 0;
				}
			} catch (final ContradictionException e) {
				throw new org.prop4j.solver.ContradictionException();
			}
		}
		return 0;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#push(org.prop4j.Node[])
	 */
	@Override
	public int push(Node... formulas) throws org.prop4j.solver.ContradictionException {
		int newClauses = 0;
		for (int i = 0; i < formulas.length; i++) {
			newClauses += push(formulas[i]);
		}
		return newClauses;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getSoulution()
	 */
	@Override
	public Object[] getSolution() {
		final int[] model = solver.model();
		if (model == null) {
			return null;
		}
		return SolverUtils.getObjectModel(model);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#findSolution()
	 */
	@Override
	public Object[] findSolution() {
		if (isSatisfiable() == ISatResult.TRUE) {
			return getSolution();
		}
		return null;
	}

	/**
	 * Returns the native solver.
	 *
	 * @return native solver
	 */
	public Solver<?> getInternalSolver() {
		if (solver instanceof Solver<?>) {
			return (Solver<?>) solver;
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#setConfiguration(java.lang.String, java.lang.Object)
	 */
	@Override
	public boolean setConfiguration(String key, Object value) {
		if (value == null) {
			return false;
		}
		switch (key) {
		case CONFIG_TIMEOUT:
			if (value instanceof Integer) {
				final int timeout = (int) value;
				solver.setTimeoutMs(timeout);
				return true;
			}
		case CONFIG_VERBOSE:
			if (value instanceof Boolean) {
				final boolean verbose = (boolean) value;
				solver.setVerbose(verbose);
				return true;
			}
		case CONFIG_DB_SIMPLIFICATION_ALLOWED:
			if (value instanceof Boolean) {
				final boolean dbSimpiAllowed = (boolean) value;
				solver.setDBSimplificationAllowed(dbSimpiAllowed);
				return true;
			}
		case CONFIG_SELECTION_STRATEGY:
			if (value instanceof SelectionStrategy) {
				final SelectionStrategy strategy = (SelectionStrategy) value;
				switch (strategy) {
				case NEGATIVE:
					if (solver instanceof Solver<?>) {
						((Solver<?>) solver).setOrder(new VarOrderHeap2(new NegativeLiteralSelectionStrategy(), order));
					}
					return true;
				case ORG:
					if (solver instanceof Solver<?>) {
						((Solver<?>) solver).setOrder(new VarOrderHeap(new RSATPhaseSelectionStrategy()));
					}
					return true;
				case POSITIVE:
					if (solver instanceof Solver<?>) {
						((Solver<?>) solver).setOrder(new VarOrderHeap2(new PositiveLiteralSelectionStrategy(), order));
					}
					return true;
				case RANDOM:
					if (solver instanceof Solver<?>) {
						((Solver<?>) solver).setOrder(new VarOrderHeap2(new RandomLiteralSelectionStrategy(), order));
					}
					return true;
				default:
					break;
				}
			}
			break;
		default:
			break;
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getIndexOfClause(org.prop4j.Node)
	 */
	@Override
	public int getIndexOfClause(Node clause) {
		return memory.getIndexOfNode(clause);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getClauseOfIndex(int)
	 */
	@Override
	public Node getClauseOfIndex(int index) {
		return memory.getNodeOfIndex(index);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getClauses()
	 */
	@Override
	public List<Node> getClauses() {
		if ((getProblem() == null) || (getProblem().getClauseCount() == 0)) {
			return null;
		}
		return memory.getAllClauses();
	}
}
