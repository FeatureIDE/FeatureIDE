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
package org.prop4j.explain.solvers;

import java.util.List;
import java.util.Set;

import org.prop4j.Node;

/**
 * A solver capable of extracting a {@link #getMinimalUnsatisfiableSubset() minimal unsatisfiable subset (MUS)} from a propositional formula.
 *
 * @author Timo G&uuml;nther
 */
public interface MusExtractor extends MutableSatSolver {

	/**
	 * <p> Returns any minimal unsatisfiable subset (MUS) of the problem. A MUS is any unsatisfiable subset of the formula which cannot be reduced any further
	 * without becoming satisfiable. </p>
	 *
	 * <p> A MUS can act as an explanation for why a formula is unsatisfiable. As such, the problem must be {@link #isSatisfiable() unsatisfiable} for a MUS to
	 * be found. </p>
	 *
	 * @return any minimal unsatisfiable subset; not null
	 * @throws IllegalStateException if the formula in this solver is satisfiable
	 */
	public Set<Node> getMinimalUnsatisfiableSubset() throws IllegalStateException;

	/**
	 * Returns any minimal unsatisfiable subset (MUS) of the problem. Each clause is referenced by its index instead of object.
	 *
	 * @return any minimal unsatisfiable subset; not null
	 * @throws IllegalStateException if the formula in this solver is satisfiable
	 */
	public Set<Integer> getMinimalUnsatisfiableSubsetIndexes() throws IllegalStateException;

	/**
	 * Returns all minimal unsatisfiable subsets of the problem.
	 *
	 * @return all minimal unsatisfiable subsets of the problem
	 * @throws IllegalStateException if the formula in this solver is satisfiable
	 */
	public List<Set<Node>> getAllMinimalUnsatisfiableSubsets() throws IllegalStateException;

	/**
	 * Returns all minimal unsatisfiable subsets of the problem referenced by index.
	 *
	 * @return all minimal unsatisfiable subsets of the problem referenced by index.
	 * @throws IllegalStateException if the formula in this solver is satisfiable
	 */
	public List<Set<Integer>> getAllMinimalUnsatisfiableSubsetIndexes() throws IllegalStateException;
}
