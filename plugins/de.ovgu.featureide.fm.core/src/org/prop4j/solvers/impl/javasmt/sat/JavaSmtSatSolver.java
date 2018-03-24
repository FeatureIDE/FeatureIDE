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

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatResult;
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
	protected SolverContext context;
	/** Memory for the solver. Holds information about the pushed and static formulas. For the JavaSMT and Prop4J nodes. */
	protected SolverMemory<BooleanFormula> pushstack;
	/** Translator used to transform prop4j nodes to JavaSMT formulas. */
	protected Prop4JToJavaSmtTranslator translator;
	/** Native Environment of JavaSMT used to solve the query's */
	protected ProverEnvironment prover;
	/** Configuration option for JavaSMT solver to determine the solver used. @link Solvers */
	public static final String SOLVER_TYPE = "solver_type";

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
	public ISatResult isSatisfiable() {
		try {
			final List<BooleanFormula> formulas = pushstack.getAssumtions();
			final boolean isSat = !prover.isUnsatWithAssumptions(formulas);
			return isSat ? ISatResult.TRUE : ISatResult.FALSE;
		} catch (final SolverException e) {
			return ISatResult.TIMEOUT;
		} catch (final InterruptedException e) {
			return ISatResult.TIMEOUT;
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
		if (!(node instanceof Literal) || ((node.getChildren() != null) && (node.getChildren().length != 1))) {
			// Is clause so pop from context
			prover.pop();
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
	 * @see org.prop4j.solver.ISolver#push(org.prop4j.Node)
	 */
	@Override
	public int push(Node formula) {
		if ((formula instanceof Literal) || (formula instanceof Or)) {
			final BooleanFormula formulaJavaSmt = translator.getFormula(formula);
			pushstack.push(formula, formulaJavaSmt);
			if ((formula instanceof Literal)) {
				return 0;
			} else {
				try {
					prover.push(formulaJavaSmt);
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
		try {
			if (!prover.isUnsatWithAssumptions(pushstack.getAssumtions())) {
				final Model model = prover.getModel();
				final Iterator<ValueAssignment> iterator = model.iterator();
				final List<Integer> solution = new ArrayList<>();
				while (iterator.hasNext()) {
					final ValueAssignment value = iterator.next();
					if (value.getValue().toString().equals("true")) {
						solution.add(Integer.parseInt(value.getName()));
					} else {
						solution.add(-Integer.parseInt(value.getName()));
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
		return pushstack.getAllClauses();
	}

}
