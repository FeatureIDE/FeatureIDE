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
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Stack;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatResult;
import org.prop4j.solver.impl.SolverUtils;
import org.prop4j.solverOld.VarOrderHeap2;
import org.prop4j.solvers.impl.javasmt.sat.SolverMemory;
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

import de.ovgu.featureide.fm.core.FMCorePlugin;

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
	protected Stack<Node> pushstack = new Stack<>();
	/** the pseudo clause. */
	protected IConstr pseudoClause;
	/**
	 * Holds information about all pushed clauses and the ability to retrieve their index. Keep in mind that the indexes need to be subtracted by 1 (2) because
	 * Sat4J only supports index from 1 (and that the first added clause is a pseudo clause which is always true.)
	 */
	protected SolverMemory<IConstr> memory;

	public Sat4jSatSolver(ISatProblem problem, Map<String, Object> config) {
		super(problem);

		// Init Solver with configuration
		solver = createSolver();
		solver.setTimeoutMs(1000);
		solver.setDBSimplificationAllowed(true);
		solver.setVerbose(false);
		setConfiguration(config);

		// +1 because Sat4J accept no variable index of 0
		final int numberOfVariables = problem.getNumberOfVariables() + 1;
		order = new int[numberOfVariables];

		// create the variables for Sat4J
		registerVariables();
	}

	public Sat4jSatSolver(ISatProblem problem) {
		super(problem);

		// Init Solver with configuration
		solver = createSolver();
		solver.setTimeoutMs(1000);
		solver.setDBSimplificationAllowed(true);
		solver.setVerbose(false);

		// +1 because Sat4J accept no variable index of 0
		final int numberOfVariables = problem.getNumberOfVariables() + 1;
		order = new int[numberOfVariables];

		// create the variables for Sat4J
		registerVariables();
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
	private void registerVariables() {
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
			throw new RuntimeException();
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
			FMCorePlugin.getDefault().logError(e);
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
			final IConstr constraint = memory.popFormula();
			if (constraint != null) {
				solver.removeSubsumedConstr(constraint);
				solver.clearLearntClauses();
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
	 * @see org.prop4j.solver.ISolver#push(org.prop4j.Node)
	 */
	@Override
	public void push(Node formula) throws org.prop4j.solver.ContradictionException {
		if (formula instanceof Literal) {
			final Literal literal = (Literal) formula;
			assignment.push(getProblem().getSignedIndexOfVariable(literal));
			pushstack.push(formula);
		} else if (formula instanceof Or) {
			try {
				final Node[] children = formula.getChildren();
				final int[] clause = new int[children.length];
				for (int i = 0; i < children.length; i++) {
					final Literal literal = (Literal) children[i];
					clause[i] = getProblem().getSignedIndexOfVariable(literal);
				}
				memory.push(formula, solver.addClause(new VecInt(clause)));
				pushstack.push(formula);
			} catch (final ContradictionException e) {
				FMCorePlugin.getDefault().logError("Cannot push formula \"" + formula + "\" to the solver because it would lead to a contradiction", e);
				throw new org.prop4j.solver.ContradictionException();
			}

		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#push(org.prop4j.Node[])
	 */
	@Override
	public void push(Node... formulas) throws org.prop4j.solver.ContradictionException {
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
		return SolverUtils.getObjectModel(model);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#findSolution()
	 */
	@Override
	public Object[] findSolution() {
		if (isSatisfiable() == ISatResult.TRUE) {
			return getSoulution();
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
			}
			return true;
		case CONFIG_VERBOSE:
			if (value instanceof Boolean) {
				final boolean verbose = (boolean) value;
				solver.setVerbose(verbose);
			}
			return true;
		case CONFIG_DB_SIMPLIFICATION_ALLOWED:
			if (value instanceof Boolean) {
				final boolean dbSimpiAllowed = (boolean) value;
				solver.setDBSimplificationAllowed(dbSimpiAllowed);
			}
			return true;
		case CONFIG_SELECTION_STRATEGY:
			if (value instanceof SatSolverSelectionStrategy) {
				final SatSolverSelectionStrategy strategy = (SatSolverSelectionStrategy) value;
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
}
