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

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.prop4j.Node;
import org.prop4j.solver.IMusExtractor;
import org.prop4j.solver.ISatProblem;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * JavaSMT sat solver used to extract unsatisfiable cores from sat query's.
 *
 * @author Joshua Sprey
 */
public class JavaSmtSatMusExtractor extends JavaSmtSatSolver implements IMusExtractor {

	/**
	 * @param problem
	 * @param solver
	 * @param configuration
	 */
	public JavaSmtSatMusExtractor(ISatProblem problem, Solvers solver, Map<String, Object> configuration) {
		super(problem, solver, configuration);
		prover.close();
		prover =
			context.newProverEnvironment(ProverOptions.GENERATE_MODELS, ProverOptions.GENERATE_UNSAT_CORE, ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
		for (final BooleanFormula staticFormula : pushstack.getFormulasAsList()) {
			try {
				prover.addConstraint(staticFormula);
			} catch (final InterruptedException e) {}
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.IMusExtractor#getMinimalUnsatisfiableSubset()
	 */
	@Override
	public Set<Node> getMinimalUnsatisfiableSubset() throws IllegalStateException {
		try {
			if (prover.isUnsatWithAssumptions(pushstack.getAssumtions())) {
				final List<BooleanFormula> formula = prover.getUnsatCore();
				final Set<Node> explanation = new HashSet<>();
				final List<BooleanFormula> assumptions = pushstack.getAssumtions();
				for (int i = 0; i < formula.size(); i++) {
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

}
