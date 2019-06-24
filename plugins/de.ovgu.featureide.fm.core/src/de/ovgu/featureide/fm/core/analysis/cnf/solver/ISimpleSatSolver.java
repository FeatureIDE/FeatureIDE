/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf.solver;

import java.util.List;

import org.sat4j.specs.IConstr;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.IInternalVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public interface ISimpleSatSolver extends Cloneable {

	/**
	 * Possible outcomes of a satisfiability solver call.<br/> One of {@code TRUE}, {@code FALSE}, or {@code TIMEOUT}.
	 *
	 * @author Sebastian Krieter
	 */
	public static enum SatResult {
		FALSE, TIMEOUT, TRUE
	}

	/**
	 * Adds a clause.
	 *
	 * @param mainClause The clause to add.
	 *
	 * @return The identifying constraint object of the clause that can be used to remove it from the solver.
	 *
	 * @see #removeClause(IConstr)
	 * @see #addClauses(Iterable)
	 */
	IConstr addClause(LiteralSet mainClause) throws RuntimeContradictionException;

	IConstr addInternalClause(LiteralSet mainClause) throws RuntimeContradictionException;

	/**
	 * Adds multiple clauses.
	 *
	 * @param clauses A collection of clauses.
	 *
	 * @return A list of the identifying constraint objects of the added clauses that can be used to remove them from the solver.
	 *
	 * @see #removeClause(IConstr)
	 * @see #addClause(LiteralSet)
	 */
	List<IConstr> addClauses(Iterable<? extends LiteralSet> clauses) throws RuntimeContradictionException;

	List<IConstr> addInternalClauses(Iterable<? extends LiteralSet> clauses) throws RuntimeContradictionException;

	/**
	 * Removes a certain clause. If possible, instead of using this method consider using {@link #removeLastClause()} as it runs faster.<br/> <b>Note:</b> This
	 * method may not be supported by all solvers.
	 *
	 * @param constr The identifying constraint object for the clause.
	 *
	 * @see #addClauses(Iterable)
	 * @see #addClause(LiteralSet)
	 */
	void removeClause(IConstr constr);

	/**
	 * Removes the last clause added to the solver. This method should be preferred over {@link #removeClause(IConstr)}, if possible.<br/> <b>Note:</b> This
	 * method may not be supported by all solvers.
	 *
	 * @see #addClauses(Iterable)
	 * @see #addClause(LiteralSet)
	 */
	void removeLastClause();

	/**
	 * Removes the last clauses added to the solver. This method should be preferred over {@link #removeClause(IConstr)}, if possible.<br/> <b>Note:</b> This
	 * method may not be supported by all solvers.
	 *
	 * @param numberOfClauses The number of clauses that should be removed.
	 *
	 * @see #addClauses(Iterable)
	 * @see #addClause(LiteralSet)
	 */
	void removeLastClauses(int numberOfClauses);

	/**
	 * @return A new instance of the solver.
	 */
	ISimpleSatSolver clone();

	/**
	 * Checks whether there is a satisfying solution considering the clauses of the solver.
	 *
	 * @return A {@link SatResult}.
	 *
	 * @see #hasSolution(LiteralSet)
	 * @see #hasSolution(int...)
	 * @see #getSolution()
	 */
	SatResult hasSolution();

	/**
	 * Checks whether there is a satisfying solution considering the clauses of the solver and the given variable assignment.
	 *
	 * @param assignment The temporarily variable assignment for this call.
	 * @return A {@link SatResult}.
	 *
	 * @see #hasSolution(LiteralSet)
	 * @see #hasSolution()
	 * @see #getSolution()
	 */
	SatResult hasSolution(int... assignment);

	/**
	 * Checks whether there is a satisfying solution considering the clauses of the solver and the given variable assignment.
	 *
	 * @param assignment The temporarily variable assignment for this call.
	 * @return A {@link SatResult}.
	 *
	 * @see #hasSolution()
	 * @see #hasSolution(int...)
	 * @see #getSolution()
	 */
	SatResult hasSolution(LiteralSet assignment);

	/**
	 * Returns the last solution found by satisfiability solver. Can only be called after a successful call of {@link #hasSolution()} or
	 * {@link #hasSolution(int...)}.
	 *
	 * @return An int array representing the satisfying assignment.
	 *
	 * @see #hasSolution()
	 * @see #hasSolution(int...)
	 */
	int[] getSolution();

	int[] getInternalSolution();

	/**
	 * @return The {@link CNF sat instance} given to the solver.
	 */
	CNF getSatInstance();

	/**
	 * Completely resets the solver, removing all its assignments, variables, and clauses.
	 */
	void reset();

	void setTimeout(int timeout);

	IInternalVariables getInternalMapping();

}
