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

import java.util.Map;

import org.prop4j.Node;

/**
 * A solver for the satisfiability problem for propositional formulas. Uses a SAT oracle to do the actual work and only provides a common access point.
 *
 * @author Timo G&uuml;nther
 * @see {@link MutableSatSolver} for a solver that supports the removal of clauses
 */
public interface SatSolver extends SatProblem {

	/**
	 * Returns the oracle used for the actual solving.
	 *
	 * @return the oracle; not null
	 */
	public Object getOracle();

	/**
	 * <p> Returns true iff the problem is satisfiable. </p>
	 *
	 * <p> More formally, let <i>f</i> denote the current (possibly empty) problem. Those are all the clauses that have been {@link #addFormula(Node) added} to
	 * the problem. <i>f</i> is a conjunction of <i>n</i> &ge; 0 CNF clauses <i>f<sub>i</sub></i>. Each clause <i>f<sub>i</sub></i> in turn consists of a
	 * positive amount of possibly negated literals <i>f<sub>ij</sub></i>: </p>
	 *
	 * <p> <blockquote><i>f</i> = <i>f<sub>1</sub></i> &and; &hellip; &and; <i>f<sub>n</sub></i><br> &nbsp; = (<i>f<sub>11</sub></i> &or; &hellip; &or;
	 * <i>f<sub>1m</sub></i>) &and; &hellip; &and; (<i>f<sub>n1</sub></i> &or; &hellip; &or; <i>f<sub>nk</sub></i>)</blockquote> </p>
	 *
	 * </p> Then, <i>f</i> is satisfiable iff there is a variable assignment that satisfies <i>f</i> (i.e. makes it evaluate to true). Such an assignment is
	 * called {@link #getModel() model}. </p>
	 *
	 * @return whether the problem is satisfiable
	 */
	public boolean isSatisfiable();

	/**
	 * Returns any variable assignment that {@link #isSatisfiable() satisfies} the problem.
	 *
	 * @return the model; not null
	 * @throws IllegalStateException if the problem is unsatisfiable
	 */
	public Map<Object, Boolean> getModel() throws IllegalStateException;
}
