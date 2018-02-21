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
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import org.prop4j.Node;
import org.prop4j.solver.AbstractSmtSolver;
import org.prop4j.solver.IMusExtractor;
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
import org.sosy_lab.common.rationals.Rational;
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
public class JavaSmtSolver extends AbstractSmtSolver implements IMusExtractor, IOptimizationSolver {

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
			translator = new Prop4JToJavaSmtTranslator(context);
			final List<BooleanFormula> clauses = new ArrayList<>();
			for (final Node node : getProblem().getClauses()) {
				final BooleanFormula formula = translator.getFormula(node);
				clauses.add(formula);
			}
			pushstack = new SolverMemory<>(problem, clauses);
			setConfiguration(configuration);
		} catch (final InvalidConfigurationException e) {
			FMCorePlugin.getDefault().logError(e);
		}
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
		case SOLVER_TYPE:
			try {
				if (value instanceof Solvers) {
					final Solvers solverType = (Solvers) value;
					context = SolverContextFactory.createSolverContext(config, logManager, shutdownManager.getNotifier(), solverType);
					translator = new Prop4JToJavaSmtTranslator(context);
					final List<BooleanFormula> clauses = new ArrayList<>();
					for (final Node node : getProblem().getClauses()) {
						final BooleanFormula formula = translator.getFormula(node);
						clauses.add(formula);
					}
					pushstack = new SolverMemory<>(getProblem(), clauses);
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
		return pushstack.pop();
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
	public void push(Node formula) {
		final BooleanFormula formulaJavaSmt = translator.getFormula(formula);
		pushstack.push(formula, formulaJavaSmt);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#push(org.prop4j.Node[])
	 */
	@Override
	public void push(Node... formulas) {
		for (final Node node : formulas) {
			push(node);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolver#getSoulution()
	 */
	@Override
	public Object[] getSoulution() {
		try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
			final List<BooleanFormula> usedConstraint = pushstack.getFormulasAsList();
			for (final BooleanFormula booleanFormula : usedConstraint) {
				prover.addConstraint(booleanFormula);
			}
			if (!prover.isUnsat()) {
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
		return getSoulution();
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.IMusExtractor#getMinimalUnsatisfiableSubset()
	 */
	@Override
	public Set<Node> getMinimalUnsatisfiableSubset() throws IllegalStateException {
		try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE)) {
			// Get all formulas but without assumption
			final List<BooleanFormula> usedConstraint = pushstack.getFormulasAsList();
			for (final BooleanFormula booleanFormula : usedConstraint) {
				prover.addConstraint(booleanFormula);
			}
			if (prover.isUnsat()) {
				final List<BooleanFormula> formula = prover.getUnsatCore();
				final List<BooleanFormula> assumptions = pushstack.getAssumtions();
				final Set<Node> explanation = new HashSet<>();
				for (int i = 0; i < formula.size(); i++) {
					// Don't add assumptions to unsat core
					if (!assumptions.contains(formula.get(i))) {
						explanation.add(pushstack.getNodeOfFormula(formula.get(i)));
					}
				}
				return explanation;
			}
		} catch (final SolverException e) {
			return null;
		} catch (final InterruptedException e) {
			return null;
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.IMusExtractor#getMinimalUnsatisfiableSubsetIndexes()
	 */
	@Override
	public Set<Integer> getMinimalUnsatisfiableSubsetIndexes() throws IllegalStateException {
		final Set<Node> mut = getMinimalUnsatisfiableSubset();
		final Set<Integer> explanation = new HashSet<>();
		for (final Node node : mut) {
			explanation.add(pushstack.getIndexOfNode(node));
		}
		return explanation;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.IMusExtractor#getAllMinimalUnsatisfiableSubsets()
	 */
	@Override
	public List<Set<Node>> getAllMinimalUnsatisfiableSubsets() throws IllegalStateException {
		return Collections.singletonList(getMinimalUnsatisfiableSubset());
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.IMusExtractor#getAllMinimalUnsatisfiableSubsetIndexes()
	 */
	@Override
	public List<Set<Integer>> getAllMinimalUnsatisfiableSubsetIndexes() throws IllegalStateException {
		return Collections.singletonList(getMinimalUnsatisfiableSubsetIndexes());
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
		try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
			final List<BooleanFormula> usedConstraint = pushstack.getFormulasAsList();
			for (final BooleanFormula booleanFormula : usedConstraint) {
				prover.addConstraint(booleanFormula);
			}
			final NumeralFormula formula = translator.getVariables().get(variable);
			final int handleY = prover.minimize(formula);
			final OptStatus status = prover.check();
			assert status == OptStatus.OPT;
			final Optional<Rational> lower = prover.lower(handleY, Rational.ofString("1/1000"));
			return lower.get();
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
		try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
			final List<BooleanFormula> usedConstraint = pushstack.getFormulasAsList();
			for (final BooleanFormula booleanFormula : usedConstraint) {
				prover.addConstraint(booleanFormula);
			}
			final NumeralFormula formula = translator.getVariables().get(variable);
			final int handleX = prover.maximize(formula);
			final OptStatus status = prover.check();
			assert status == OptStatus.OPT;
			final Optional<Rational> upper = prover.upper(handleX, Rational.ofString("1/1000"));
			return upper.get();
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
		try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
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
			final Optional<Rational> lower = prover.lower(handleY, Rational.ofString("1/1000"));
			result[0] = lower.get();

			// max
			final int handleX = prover.maximize(formula);
			final OptStatus statusMax = prover.check();
			assert statusMax == OptStatus.OPT;
			final Optional<Rational> upper = prover.upper(handleX, Rational.ofString("1/1000"));
			result[1] = upper.get();
			return result;
		} catch (final InterruptedException e) {} catch (final SolverException e) {
			e.printStackTrace();
		}
		return null;
	}

}
