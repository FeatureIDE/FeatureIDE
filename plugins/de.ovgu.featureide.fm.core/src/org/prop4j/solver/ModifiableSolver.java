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
package org.prop4j.solver;

import java.util.LinkedList;
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

/**
 * Finds certain solutions of propositional formulas.
 * Clauses can be removed.
 * 
 * @author Sebastian Krieter
 */
public class ModifiableSolver extends BasicSolver {

	public ModifiableSolver(SatInstance satInstance) throws ContradictionException {
		super(satInstance);
	}

	protected ModifiableSolver(ModifiableSolver oldSolver) {
		super(oldSolver);
	}

	protected Solver<?> initSolver() {
		final Solver<?> solver = (Solver<?>) SolverFactory.newDefault();
		solver.setTimeoutMs(1000);
		solver.setDBSimplificationAllowed(false);
		solver.setVerbose(false);
		return solver;
	}

	public List<IConstr> addClauses(Node constraint) throws ContradictionException {
		return addCNF(constraint.getChildren());
	}

	protected List<IConstr> addCNF(final Node[] cnfChildren) throws ContradictionException {
		final List<IConstr> result = new LinkedList<>();
		try {
			for (Node node : cnfChildren) {
				final Node[] children = node.getChildren();
				final int[] clause = new int[children.length];
				for (int i = 0; i < children.length; i++) {
					final Literal literal = (Literal) children[i];
					clause[i] = satInstance.getSignedVariable(literal);
				}
				result.add(solver.addClause(new VecInt(clause)));
			}
		} catch (ContradictionException e) {
			for (IConstr constr : result) {
				if (constr != null) {
					solver.removeConstr(constr);
				}
			}
			throw e;
		}
		return result;
	}

	public void removeConstraint(IConstr constr) {
		solver.removeConstr(constr);
	}

	public boolean isImplied(Node... or) {
		final IVecInt backbone = new VecInt();
		for (int i = 0; i < or.length; i++) {
			final Literal node = (Literal) or[i];
			backbone.push(-satInstance.getSignedVariable(node));
		}
		try {
			return !solver.isSatisfiable(backbone);
		} catch (TimeoutException e) {
			Logger.logError(e);
		}
		return false;
	}

	@Override
	public ModifiableSolver clone() {
		return new ModifiableSolver(this);
	}

}
