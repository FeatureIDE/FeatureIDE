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

import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.prop4j.Node;

/**
 * <p> Facade for the satisfiability problem for propositional formulas. </p>
 *
 * <p> Note that this interface only requires the bare minimum. In particular, clauses may only be {@link #addFormula(Node) added} but never removed. </p>
 *
 * @author Timo G&uuml;nther
 * @see {@link SatSolver} for solving the problem
 */
public interface SatProblem {

	/**
	 * <p> Adds all given formulas to the problem. First, each given formula is converted to {@link Node#isClausalNormalForm() clausal normal form (CNF)}. Then,
	 * each clause of the resulting conjunction is added to the existing conjunction. Ignores clauses already added. </p>
	 *
	 * <p> More formally, let <i>f</i> denote the current (possibly empty) formula in the problem. After this operation, the problem contains the formula
	 * <i>f'</i>. <i>f'</i> is the conjunction of <i>f</i> with each of the <i>m</i> &ge; 0 (possibly empty) given formulas <i>g<sub>j</sub></i> in CNF: </p>
	 *
	 * <p> <blockquote><i>f'</i> = <i>f</i> &and; <i>g<sub>1</sub></i> &and; &hellip; &and; <i>g<sub>m</sub></i></blockquote> </p>
	 *
	 * @param formulas formulas to add; not null
	 * @return the amount of clauses added
	 */
	public int addFormulas(Node... formulas);

	/**
	 * <p> Adds all given formulas to the problem. First, each given formula is converted to {@link Node#isClausalNormalForm() clausal normal form (CNF)}. Then,
	 * each clause of the resulting conjunction is added to the existing conjunction. Ignores clauses already added. </p>
	 *
	 * <p> More formally, let <i>f</i> denote the current (possibly empty) formula in the problem. After this operation, the problem contains the formula
	 * <i>f'</i>. <i>f'</i> is the conjunction of <i>f</i> with each of the <i>m</i> &ge; 0 (possibly empty) given formulas <i>g<sub>j</sub></i> in CNF: </p>
	 *
	 * <p> <blockquote><i>f'</i> = <i>f</i> &and; <i>g<sub>1</sub></i> &and; &hellip; &and; <i>g<sub>m</sub></i></blockquote> </p>
	 *
	 * @param formulas formulas to add; not null
	 * @return the amount of clauses added
	 */
	public int addFormulas(Collection<? extends Node> formulas);

	/**
	 * <p> Adds the given formula to the problem. First, the given formula is converted to {@link Node#isClausalNormalForm() clausal normal form (CNF)}. Then,
	 * each clause of the resulting conjunction is added to the existing conjunction. Ignores clauses already added. </p>
	 *
	 * <p> More formally, let <i>f</i> denote the current (possibly empty) formula in the problem. After this operation, the problem contains the formula
	 * <i>f'</i>. <i>f'</i> is the conjunction of <i>f</i> with the (possibly empty) given formula <i>g</i> in CNF: </p>
	 *
	 * <p> <blockquote><i>f'</i> = <i>f</i> &and; <i>g</i></blockquote> </p>
	 *
	 * @param formula formula to add; not null
	 * @return the amount of clauses added
	 */
	public int addFormula(Node formula);

	/**
	 * Returns all clauses in this problem.
	 *
	 * @return all clauses in this problem; not null
	 */
	public List<Node> getClauses();

	/**
	 * Returns the clauses with the given indexes.
	 *
	 * @param indexes clause indexes
	 * @return the clauses with the given indexes
	 * @throws IndexOutOfBoundsException if any index is out of range
	 */
	public List<Node> getClauses(Collection<Integer> indexes) throws IndexOutOfBoundsException;

	/**
	 * Returns the clause at the given index.
	 *
	 * @param index index of the clause
	 * @return the clause at the given index; not null
	 * @throws IndexOutOfBoundsException if the index is out of range, that is negative or greater than or equal to the {@link #getClauseCount() amount of
	 *         clauses}
	 */
	public Node getClause(int index) throws IndexOutOfBoundsException;

	/**
	 * Returns the amount of clauses in this problem.
	 *
	 * @return the amount of clauses in this problem
	 */
	public int getClauseCount();

	/**
	 * Returns true if this contains a clause that equals the given clause.
	 *
	 * @param clause clause to search for
	 * @return true if this contains a clause that equals the given clause
	 */
	public boolean containsClause(Node clause);

	/**
	 * Adds all given assumptions to the problem.
	 *
	 * @param assumptions assumptions to add; not null
	 */
	public void addAssumptions(Map<Object, Boolean> assumptions);

	/**
	 * Adds the given assumption to the problem.
	 *
	 * @param variable variable of which to assume the truth value; not null
	 * @param value truth value to assume
	 */
	public void addAssumption(Object variable, boolean value);

	/**
	 * Returns the truth value assumption for all variables.
	 *
	 * @return all assumptions; not null
	 */
	public Map<Object, Boolean> getAssumptions();

	/**
	 * Returns the truth value assumption for the given variable.
	 *
	 * @param variable variable of which to check the truth value
	 * @return the assumption; null if no assumption is made for the given variable
	 */
	public Boolean getAssumption(Object variable);
}
