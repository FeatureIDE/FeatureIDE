/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.prop4j.Node;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.IMusExtractor;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.SatResult;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.xplain.Xplain;

/**
 * Extends the {@link Sat4JSatSolver} by providing the functionality to calculate the minimal unsatisfiable subset for the given problem. The extracaction of
 * the subset is only possible when the current problem is not satisfiable.
 *
 * <br><br> Sat4J only support the extraction of one minimal unsatisfiable subset, thus, {@link #getAllMinimalUnsatisfiableSubsetIndexes()} and
 * {@link #getAllMinimalUnsatisfiableSubsets()} only return one solution.
 *
 * <br><br>Note: The usage of a solver to solve expression and to find minimal unsatisfiable subset should be divided into two task because the native solver
 * for the MUS extractor are by far solver in solving satisfiability requests. If solving is focused the usage of the {@link Sat4JSatSolver} is recommended
 * which uses a different native solver.
 *
 * @author Joshua Sprey
 */
public class Sat4JSatMusSolver extends Sat4JSatSolver implements IMusExtractor {

	public Sat4JSatMusSolver(ISatProblem problem, Map<String, Object> config) throws ContradictionException {
		super(problem, config);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.impl.sat4j.Sat4jSatSolverNew#getSolver()
	 */
	@SuppressWarnings("unchecked")
	@Override
	protected Xplain<ISolver> getSolver() {
		return (Xplain<ISolver>) solver;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.impl.sat4j.Sat4jSatSolverNew#createSolver()
	 */
	@Override
	protected ISolver createSolver() {
		return new Xplain<ISolver>(super.createSolver());
	}

	@Override
	public Set<Node> getMinimalUnsatisfiableSubset() throws IllegalStateException {
		final Set<Integer> mut = getMinimalUnsatisfiableSubsetIndexes();
		final Set<Node> explanation = new HashSet<>();
		for (final Integer index : mut) {
			// Subtraction not needed because it was already done in the getMinimalUnsatisfiableSubsetIndexes method.
			explanation.add(memory.getNodeOfIndex(index));
		}
		return explanation;
	}

	@Override
	public Set<Integer> getMinimalUnsatisfiableSubsetIndexes() throws IllegalStateException {
		if (isSatisfiable() == SatResult.TRUE) {
			throw new IllegalStateException("Problem is satisfiable");
		}
		final int[] indexes;
		try {
			indexes = getSolver().minimalExplanation();
		} catch (final TimeoutException e) {
			throw new IllegalStateException(e);
		}
		final Set<Integer> set = new TreeSet<>();
		for (final int index : indexes) {
			// Subtract by 1 because index by Sat4J start by 1 and the first clause is a pseudo clause.
			set.add(index - 1);
		}
		return set;
	}

	@Override
	public List<Set<Node>> getAllMinimalUnsatisfiableSubsets() throws IllegalStateException {
		return Collections.singletonList(getMinimalUnsatisfiableSubset());
	}

	@Override
	public List<Set<Integer>> getAllMinimalUnsatisfiableSubsetIndexes() throws IllegalStateException {
		return Collections.singletonList(getMinimalUnsatisfiableSubsetIndexes());
	}
}
