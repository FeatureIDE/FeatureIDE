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
package org.prop4j.solvers.impl.javasmt.smt;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.AbstractSmtSolver;
import org.prop4j.solver.IOptimizationSolver;
import org.prop4j.solver.ISatResult;
import org.prop4j.solver.ISmtProblem;
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
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Solver used to sovle smt querys.
 *
 * @author Joshua Sprey
 */
public class JavaSmtSolver extends AbstractSmtSolver implements IOptimizationSolver {

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
	/** Configuration option for JavaSMT solver to determine the solver used. @link Solvers */
	public static final String SOLVER_TYPE = "solver_type";
	/** Engine to use for the optimization. [basic, farkas, symba] */
	public static final String OPTIMIZATION_ENGINE = "OptimizationEngine";
	/** Ordering for objectives in the optimization context. [lex, pareto, box] */
	public static final String OPTIMIZATION_OBJECTIVE_ORDERING = "OptimizationObjectiveOrdering";
	/** Native environment for JavaSMT to solve optimization query's */
	protected OptimizationProverEnvironment prover;

	/**
	 * @param node
	 * @param solver The solver that should be used to solve the query's
	 */
	public JavaSmtSolver(ISmtProblem problem, Solvers solver, Map<String, Object> configuration) {
		super(problem);
		try {
			config = Configuration.defaultConfiguration();
			logManager = BasicLogManager.create(config);
			shutdownManager = ShutdownManager.create();
			context = SolverContextFactory.createSolverContext(config, logManager, shutdownManager.getNotifier(), solver);
			translator = new Prop4JToJavaSmtTranslator(context, this);
			prover = context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS);
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
	 * @see org.prop4j.solver.ISolver#isSatisfiable()
	 */
	@Override
	public ISatResult isSatisfiable() {
		try (ProverEnvironment prover = context.newProverEnvironment()) {
			final List<BooleanFormula> formulas = pushstack.getFormulasAsList();
			for (final BooleanFormula booleanFormula : formulas) {
				prover.addConstraint(booleanFormula);
			}
			final boolean isSat = !prover.isUnsat();
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
		case OPTIMIZATION_ENGINE:
		case SOLVER_TYPE:
			try {
				if (value instanceof Solvers) {
					final Solvers solverType = (Solvers) value;
					context = SolverContextFactory.createSolverContext(config, logManager, shutdownManager.getNotifier(), solverType);
					translator = new Prop4JToJavaSmtTranslator(context, this);
					prover.close();
					prover = context.newOptimizationProverEnvironment();

					final List<BooleanFormula> clauses = new ArrayList<>();
					for (final Node node : getProblem().getClauses()) {
						final BooleanFormula formula = translator.getFormula(node);
						clauses.add(formula);
						prover.addConstraint(formula);
					}
					pushstack = new SolverMemory<>(getProblem(), clauses);
					return true;
				}
			} catch (final InvalidConfigurationException e) {} catch (final InterruptedException e) {}

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
		final Node node = pushstack.pop();
		if (!(node instanceof Literal) || (node.getChildren().length != 1)) {
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
		if ((formula instanceof Literal) || (formula instanceof Or)) {
			final BooleanFormula formulaJavaSmt = translator.getFormula(formula);
			pushstack.push(formula, formulaJavaSmt);
			if ((formula instanceof Literal) || (formula.getChildren().length == 1)) {
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
				final Object[] solution = new Object[getProblem().getNumberOfVariables() + 1];
				while (iterator.hasNext()) {
					final ValueAssignment value = iterator.next();
					final int index = getProblem().getIndexOfVariable(value.getName().toString());
					solution[index] = value.getValue();
				}
				return solution;
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
	 * @see org.prop4j.solver.IOptimizationSolver#minimum(java.lang.Object)
	 */
	@Override
	public Object minimum(Object variable) {
		if (!translator.getVariables().containsKey(variable)) {
			return null;
		}
		try {
			final List<BooleanFormula> usedConstraint = pushstack.getFormulasAsList();
			for (final BooleanFormula booleanFormula : usedConstraint) {
				prover.addConstraint(booleanFormula);
			}
			final NumeralFormula formula = translator.getVariables().get(variable);
			final int handleY = prover.minimize(formula);
			final OptStatus status = prover.check();
			assert status == OptStatus.OPT;
			// final Optional<Rational> lower = prover.lower(handleY, Rational.ofString("1/1000"));
			// return lower.get();
			return null;
		} catch (final InterruptedException e) {} catch (final SolverException e) {
			e.printStackTrace();
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.IOptimizationSolver#maximum(java.lang.Object)
	 */
	@Override
	public Object maximum(Object variable) {
		if (!translator.getVariables().containsKey(variable)) {
			return null;
		}
		try {
			final List<BooleanFormula> usedConstraint = pushstack.getFormulasAsList();
			for (final BooleanFormula booleanFormula : usedConstraint) {
				prover.addConstraint(booleanFormula);
			}
			final NumeralFormula formula = translator.getVariables().get(variable);
			final int handleX = prover.maximize(formula);
			final OptStatus status = prover.check();
			assert status == OptStatus.OPT;
//			final Optional<Rational> upper = prover.upper(handleX, Rational.ofString("1/1000"));
//			return upper.get();
			return null;
		} catch (final InterruptedException e) {} catch (final SolverException e) {
			e.printStackTrace();
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.IOptimizationSolver#minAndMax(java.lang.Object)
	 */
	@Override
	public Object[] minAndMax(Object variable) {
		if (!translator.getVariables().containsKey(variable)) {
			return null;
		}
		try {
			final List<BooleanFormula> usedConstraint = pushstack.getFormulasAsList();
			for (final BooleanFormula booleanFormula : usedConstraint) {
				prover.addConstraint(booleanFormula);
			}
			final NumeralFormula formula = translator.getVariables().get(variable);

			final Object[] result = new Object[2];

			// min
			final int handleY = prover.minimize(formula);
			final OptStatus statusMin = prover.check();
			assert statusMin == OptStatus.OPT;
//			final Optional<Rational> lower = prover.lower(handleY, Rational.ofString("1/1000"));
//			result[0] = lower.get();
			result[0] = null;

			// max
			final int handleX = prover.maximize(formula);
			final OptStatus statusMax = prover.check();
			assert statusMax == OptStatus.OPT;
//			final Optional<Rational> upper = prover.upper(handleX, Rational.ofString("1/1000"));
//			result[1] = upper.get();
			result[1] = null;
			return result;
		} catch (final InterruptedException e) {} catch (final SolverException e) {
			e.printStackTrace();
		}
		return null;
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
