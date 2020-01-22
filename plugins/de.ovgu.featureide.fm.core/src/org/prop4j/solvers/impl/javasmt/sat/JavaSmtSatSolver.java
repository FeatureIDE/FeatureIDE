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
package org.prop4j.solvers.impl.javasmt.sat;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.SatResult;
import org.prop4j.solvers.impl.javasmt.Prop4JToJavaSmtTranslator;
import org.prop4j.solvers.impl.javasmt.SolverMemory;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Sat Solver implemented with JavaSmt to solve sat requests. The kind of solver is specified by
 *
 * @author Joshua Sprey
 */
public class JavaSmtSatSolver extends AbstractSatSolver {

	/** Configuration for the solver. Needed for the native solver. Not really used. */
	protected Configuration config;
	/** Log manager for the solver. Needed for the native solver. Not really used. */
	protected LogManager logManager;
	/** Shutdown manager for the native solver. Can be used to interrupt and cancel a running operation. */
	protected ShutdownManager shutdownManager;
	/** The current contex of the solver. Used by the translator to translate prop4J nodes to JavaSMT formulas. */
	public SolverContext context;
	/** Memory for the solver. Holds information about the pushed and static formulas. For the JavaSMT and Prop4J nodes. */
	protected SolverMemory<BooleanFormula> pushstack;
	/** Translator used to transform prop4j nodes to JavaSMT formulas. */
	protected Prop4JToJavaSmtTranslator translator;
	/** Native Environment of JavaSMT used to solve the query's */
	public ProverEnvironment prover;
	/** Configuration option for JavaSMT solver to determine the solver used. @link Solvers */
	public static final String SOLVER_TYPE = "solver_type";

	public static long retrieveTime = 0;
	public static long convertTime = 0;
	public static long modelTime = 0;

	/**
	 * @param node
	 * @param solver The solver that should be used to solve the query's
	 */
	public JavaSmtSatSolver(ISatProblem problem, Solvers solver, Map<String, Object> configuration) {
		super(problem);
		try {
			config = Configuration.defaultConfiguration();
			logManager = BasicLogManager.create(config);
			shutdownManager = ShutdownManager.create();
			context = SolverContextFactory.createSolverContext(config, logManager, shutdownManager.getNotifier(), solver);
			translator = new Prop4JToJavaSmtTranslator(context, this);
			prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS);
			final List<BooleanFormula> clauses = new ArrayList<>();
			for (final Node node : getProblem().getClauses()) {
				final BooleanFormula formula = translator.getFormula(node);
				clauses.add(formula);
				prover.addConstraint(formula);
			}
			pushstack = new SolverMemory<>(problem, clauses);
			setConfiguration(configuration);

		} catch (final InvalidConfigurationException e) {
			FMCorePlugin.getDefault().logError(e);
		} catch (final InterruptedException e) {}
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#finalize()
	 */
	@Override
	protected void finalize() throws Throwable {
		prover.close();
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#isSatisfiable()
	 */
	@Override
	public SatResult isSatisfiable() {
		final List<BooleanFormula> formulas = pushstack.getAssumtions();
		final long t1 = System.currentTimeMillis();
		try {
			final boolean isSat = !prover.isUnsatWithAssumptions(formulas);
			currentSolveTime += (System.currentTimeMillis() - t1);
			return isSat ? SatResult.TRUE : SatResult.FALSE;
		} catch (final SolverException e) {
			currentSolveTime += (System.currentTimeMillis() - t1);
			return SatResult.TIMEOUT;
		} catch (final InterruptedException e) {
			currentSolveTime += (System.currentTimeMillis() - t1);
			return SatResult.TIMEOUT;
		}
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
		case SOLVER_TYPE:
			try {
				if (value instanceof Solvers) {
					final Solvers solverType = (Solvers) value;
					context = SolverContextFactory.createSolverContext(config, logManager, shutdownManager.getNotifier(), solverType);
					return true;
				}
			} catch (final InvalidConfigurationException e) {}

			break;
		default:
			break;
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#pop()
	 */
	@Override
	public Node pop() {
		if (pushstack.isStackEmpty()) {
			return null;
		}

		final Node node = pushstack.pop();
		// If Node is AND and is in CNF then pop all childs
		if ((node instanceof And) && node.isConjunctiveNormalForm()) {
//			pop(node.getChildren().length);
//			return node;

			// Is clause so pop from context
			final long time = System.currentTimeMillis();
			prover.pop();
			currentSolveTime += System.currentTimeMillis() - time;
			return node;
		}

		// Handle Literals
		if (node instanceof Literal) {
			// Do nothing the assumption is removed from the memory with pushstack.pop
		}

		// Handle Or Nodes
		if (node instanceof Or) {
			final Node[] children = node.getChildren();

			// Verify at least one children
			if (children.length == 0) {
				throw new UnsupportedOperationException("Cannot push Or node with zero childs");

			}

			// Verify each children as literal
			for (final Node child : children) {
				if (!(child instanceof Literal)) {
					throw new UnsupportedOperationException("Can only push Or nodes containing Literals");
				}
			}

			// Handle Or with only one Literal
			if (children.length == 1) {
				// Do nothing the assumption is removed from the memory with pushstack.pop
			} else {
				// Is clause so pop from context
				final long time = System.currentTimeMillis();
				prover.pop();
				currentSolveTime += System.currentTimeMillis() - time;
			}
		}

		return node;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#pop(int)
	 */
	@Override
	public List<Node> pop(int count) {
		final List<Node> nodes = new ArrayList<>();
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
		final int pushstackLength = pushstack.getNumberOfPushedNodes();
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
	public int push(Node formula) {
		// If Node is AND and is in CNF then push every child seperately
		if ((formula instanceof And) && formula.isConjunctiveNormalForm()) {
			final BooleanFormula formulaJavaSmt = translator.getFormula(formula);
			pushstack.push(formula, formulaJavaSmt);
			final long time = System.currentTimeMillis();
			try {
				prover.push(formulaJavaSmt);
				currentSolveTime += System.currentTimeMillis() - time;
			} catch (final InterruptedException e) {}
			return 1;
//			final int clauses = push(formula.getChildren());
//			// Put and node on stack
//			pushstack.push(formula, null);
//			return clauses;
		} else if ((formula instanceof And) && !formula.isConjunctiveNormalForm()) {
			throw new UnsupportedOperationException("The SAT solver can only handle And nodes in conjunctive normal form");
		}

		// Only accept Literals or OR nodes with Literals
		if (!(formula instanceof Literal) && !(formula instanceof Or)) {
			throw new UnsupportedOperationException("The SAT solver can only handle the node types: Or(Literals...) and Literal");
		}

		// Handle Literals
		if (formula instanceof Literal) {
			// Add as assumption
			final BooleanFormula formulaJavaSmt = translator.getFormula(formula);
			pushstack.push(formula, formulaJavaSmt);
			// Do not add directly to solver because assumptions are given as parameter to isSatisfiable
			return 0;
		}

		// Handle Or Nodes
		if (formula instanceof Or) {
			final Node[] children = formula.getChildren();

			// Verify at least one children
			if (children.length == 0) {
				throw new UnsupportedOperationException("Cannot push Or node with zero childs");

			}

			// Verify each children as literal
			for (final Node node : children) {
				if (!(node instanceof Literal)) {
					throw new UnsupportedOperationException("Can only push Or nodes containing Literals");
				}
			}

			// Handle Or with only one Literal
			if (children.length == 1) {
				// Add as assumption
				final BooleanFormula formulaJavaSmt = translator.getFormula(formula);
				pushstack.push(formula, formulaJavaSmt);
				// Do not add directly to solver because assumptions are given as parameter to isSatisfiable
				return 0;
			} else {
				// Add as formula
				final BooleanFormula formulaJavaSmt = translator.getFormula(formula);
				pushstack.push(formula, formulaJavaSmt);
				final long time = System.currentTimeMillis();
				try {
					prover.push(formulaJavaSmt);
					currentSolveTime += System.currentTimeMillis() - time;
				} catch (final InterruptedException e) {}
				return 1;
			}
		}
		return 0;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#push(org.prop4j.Node[])
	 */
	@Override
	public int push(Node... formulas) {
		int newClauses = 0;
		for (final Node node : formulas) {
			newClauses += push(node);
		}
		return newClauses;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getSoulution()
	 */
	@Override
	public Object[] getSolution() {
		final long t10 = System.currentTimeMillis();
		try {
			if (!prover.isUnsatWithAssumptions(pushstack.getAssumtions())) {
				currentSolveTime += (System.currentTimeMillis() - t10);
				final Model model = prover.getModel();
				final Iterator<ValueAssignment> iterator = model.iterator();
				final List<Integer> solution = new ArrayList<>();

				while (iterator.hasNext()) {
					final ValueAssignment value = iterator.next();
					if (value.getValue().toString().equals("true")) {
						solution.add(getProblem().getIndexOfVariable(value.getName()));
					} else {
						solution.add(-getProblem().getIndexOfVariable(value.getName()));
					}
				}
				if (solution.size() < getProblem().getNumberOfVariables()) {
					for (int i = 1; i <= getProblem().getNumberOfVariables(); i++) {
						if ((!solution.contains(i)) && (!solution.contains(-i))) {
							solution.add(-i);
						}
					}
				}

				return solution.toArray();
			} else {
				return null;
			}
		} catch (final SolverException e) {
			return null;
		} catch (final InterruptedException e) {
			return null;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#findSolution()
	 */
	@Override
	public Object[] findSolution() {
		return getSolution();
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getIndexOfClause(org.prop4j.Node)
	 */
	@Override
	public int getIndexOfClause(Node clause) {
		return pushstack.getIndexOfNode(clause);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getClauseOfIndex(int)
	 */
	@Override
	public Node getClauseOfIndex(int index) {
		return pushstack.getNodeOfIndex(index);
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
		return pushstack.getAllClauses();
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISatSolver#getIndexOfAssumptions()
	 */
	@Override
	public int[] getIndexOfAssumptions() {
		final List<BooleanFormula> formulas = pushstack.getAssumtions();
		final int[] result = new int[formulas.size()];
		for (int i = 0; i < result.length; i++) {
			final Node literal = pushstack.getNodeOfFormula(formulas.get(i));
			if (literal instanceof Literal) {
				final Literal lit = (Literal) literal;
				result[i] = getProblem().getSignedIndexOfVariable(lit);
			} else if ((literal instanceof Or) && (literal.getChildren()[0] instanceof Literal)) {
				final Literal lit = (Literal) literal.getChildren()[0];
				result[i] = getProblem().getSignedIndexOfVariable(lit);
			}
		}
		return result;
	}

	public long currentSolveTime = 0;

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISatSolver#getSolveTime()
	 */
	@Override
	public long getSolveTime() {
		final long currentT = currentSolveTime;
		resetRuntime();
		return currentT;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISatSolver#resetRuntime()
	 */
	@Override
	public void resetRuntime() {
		currentSolveTime = 0;
	}

}
