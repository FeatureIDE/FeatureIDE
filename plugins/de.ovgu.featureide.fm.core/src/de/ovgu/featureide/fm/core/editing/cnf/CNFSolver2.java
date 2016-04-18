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
package de.ovgu.featureide.fm.core.editing.cnf;

import java.util.Collection;

import org.prop4j.SatSolver;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.editing.remove.DeprecatedClause;

/**
 * Light version of {@link SatSolver}.
 * 
 * @author Sebastian Krieter
 */
public class CNFSolver2 implements ICNFSolver {

	private final int[] intMap;
	private final ISolver solver;

	public CNFSolver2(Collection<? extends Clause> clauses, boolean[] removedFeatures) {
		intMap = new int[removedFeatures.length];
		int c = 0;
		for (int i = 0; i < intMap.length; i++) {
			if (removedFeatures[i]) {
				c++;
			}
			intMap[i] = c;
		}

		solver = createSolver(removedFeatures.length - (c + 1));

		try {
			for (Clause node : clauses) {
				final int[] literals = node.getLiterals();
				int[] clause = new int[literals.length];
				System.arraycopy(literals, 0, clause, 0, clause.length);

				translate(clause);

				solver.addClause(new VecInt(clause));
			}
		} catch (ContradictionException e) {
			throw new RuntimeException(e);
		}
	}

	private void translate(int[] clause) {
		for (int i = 0; i < clause.length; i++) {
			final int k = clause[i];
			final int j = intMap[Math.abs(k)];
			clause[i] = k - (k > 0 ? j : -j);
		}
	}

	private ISolver createSolver(int size) {
		ISolver solver = SolverFactory.newDefault();
		solver.setTimeoutMs(1000);
		solver.newVar(size);
		return solver;
	}

	public boolean isSatisfiable(int[] literals) throws TimeoutException {
		final int[] unitClauses = new int[literals.length];
		System.arraycopy(literals, 0, unitClauses, 0, unitClauses.length);

		translate(unitClauses);
		return solver.isSatisfiable(new VecInt(unitClauses));
	}

	public void reset() {
		solver.reset();
	}

	/**
	 * @param mainClause
	 */
	public void addClause(DeprecatedClause mainClause) {
		final int[] literals = mainClause.literals;
		final int[] unitClauses = new int[literals.length];
		System.arraycopy(literals, 0, unitClauses, 0, unitClauses.length);

		translate(unitClauses);

		try {
			solver.addClause(new VecInt(unitClauses));
		} catch (ContradictionException e) {
			throw new RuntimeException(e);
		}

	}

}