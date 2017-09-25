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
package org.prop4j.solver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.Solver;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;

/**
 * Finds certain solutions of propositional formulas. Clauses can be removed.
 *
 * @author Sebastian Krieter
 */
public class ModifiableSolver extends BasicSolver {

	protected ArrayList<IConstr> constrList;

	public ModifiableSolver(SatInstance satInstance) throws ContradictionException {
		super(satInstance);
	}

	protected ModifiableSolver(ModifiableSolver oldSolver) {
		super(oldSolver);
	}

	@Override
	protected Solver<?> initSolver() {
		final Solver<?> solver = (Solver<?>) SolverFactory.newDefault();
		solver.setTimeoutMs(1000);
		solver.setDBSimplificationAllowed(false);
		solver.setVerbose(false);
		return solver;
	}

	public List<IConstr> addCNF(final Collection<? extends Clause> cnfChildren) throws ContradictionException {
		if (constrList == null) {
			constrList = new ArrayList<>();
		}
		final int oldSize = constrList.size();
		try {
			for (final Clause clause : cnfChildren) {
				constrList.add(solver.addClause(new VecInt(clause.getLiterals())));
			}
		} catch (final ContradictionException e) {
			removeLastClauses(constrList.size() - oldSize);
			throw e;
		}
		return new ArrayList<>(constrList.subList(oldSize, constrList.size()));
	}

	@Override
	protected List<IConstr> addCNF(final Node[] cnfChildren) throws ContradictionException {
		if (constrList == null) {
			constrList = new ArrayList<>();
		}
		final int oldSize = constrList.size();
		try {
			for (final Node node : cnfChildren) {
				final Node[] children = node.getChildren();
				final int[] clause = new int[children.length];
				for (int i = 0; i < children.length; i++) {
					final Literal literal = (Literal) children[i];
					clause[i] = satInstance.getSignedVariable(literal);
				}
				constrList.add(solver.addClause(new VecInt(clause)));
			}
		} catch (final ContradictionException e) {
			removeLastClauses(constrList.size() - oldSize);
			throw e;
		}
		return new ArrayList<>(constrList.subList(oldSize, constrList.size()));
	}

	public void removeConstraint(IConstr constr) {
		if (constr != null) {
			solver.removeConstr(constr);
		}
	}

	public boolean isImplied(Node... or) {
		final IVecInt backbone = new VecInt();
		for (int i = 0; i < or.length; i++) {
			final Literal node = (Literal) or[i];
			backbone.push(-satInstance.getSignedVariable(node));
		}
		try {
			return !solver.isSatisfiable(backbone);
		} catch (final TimeoutException e) {
			Logger.logError(e);
		}
		return false;
	}

	public void removeLastClauses(int numberOfClauses) {
		for (int i = 0; i < numberOfClauses; i++) {
			final IConstr removeLast = constrList.remove(constrList.size() - 1);
			if (removeLast != null) {
				solver.removeSubsumedConstr(removeLast);
			}
		}
		solver.clearLearntClauses();
	}

	@Override
	public ModifiableSolver clone() {
		if (this.getClass() == ModifiableSolver.class) {
			return new ModifiableSolver(this);
		} else {
			throw new RuntimeException("Cloning not supported for " + this.getClass().toString());
		}
	}

}
