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
package de.ovgu.featureide.fm.core.editing.cnf;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
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
public class CNFSolver implements ICNFSolver {

	private HashMap<Object, Integer> varToInt = null;
	private final ISolver solver;

	private boolean notSolveable = false;

	public CNFSolver(Node cnf) {
		varToInt = new HashMap<Object, Integer>();
		if (cnf instanceof And) {
			for (final Node clause : cnf.getChildren()) {
				if (clause instanceof Or) {
					for (final Node literal : clause.getChildren()) {
						final Object var = ((Literal) literal).var;
						if (!varToInt.containsKey(var)) {
							final int index = varToInt.size() + 1;
							varToInt.put(var, index);
						}
					}
				} else {
					final Object var = ((Literal) clause).var;
					if (!varToInt.containsKey(var)) {
						final int index = varToInt.size() + 1;
						varToInt.put(var, index);
					}
				}
			}
		} else if (cnf instanceof Or) {
			for (final Node literal : cnf.getChildren()) {
				final Object var = ((Literal) literal).var;
				if (!varToInt.containsKey(var)) {
					final int index = varToInt.size() + 1;
					varToInt.put(var, index);
				}
			}
		} else {
			varToInt.put(((Literal) cnf).var, 1);
		}

		solver = createSolver(varToInt.size());

		try {
			if (cnf instanceof And) {
				for (final Node andChild : cnf.getChildren()) {
					if (andChild instanceof Or) {
						final Node[] literals = andChild.getChildren();
						final int[] clause = new int[literals.length];
						int i = 0;
						for (final Node child : literals) {
							final Literal literal = (Literal) child;
							clause[i++] = literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var);
						}
						solver.addClause(new VecInt(clause));
					} else {
						final Literal literal = (Literal) andChild;
						solver.addClause(new VecInt(new int[] { literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var) }));
					}
				}
			} else if (cnf instanceof Or) {
				final Node[] literals = cnf.getChildren();
				final int[] clause = new int[literals.length];
				int i = 0;
				for (final Node child : literals) {
					final Literal literal = (Literal) child;
					clause[i++] = literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var);
				}
				solver.addClause(new VecInt(clause));
			} else {
				final Literal literal = (Literal) cnf;
				solver.addClause(new VecInt(new int[] { literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var) }));
			}
			final int size = varToInt.size();
			final VecInt pseudoClause = new VecInt(size + 1);
			for (int i = 1; i <= size; i++) {
				pseudoClause.push(i);
			}
			pseudoClause.push(-1);
			solver.addClause(pseudoClause);
		} catch (final ContradictionException e) {
			// throw new RuntimeException(e);
			notSolveable = true;
		}
	}

	public CNFSolver(Collection<? extends Clause> clauses, int size) {
		solver = createSolver(size);
		addClauses(clauses);
	}

	public CNFSolver(int size) {
		solver = createSolver(size);
	}

	public void addClauses(Collection<? extends Clause> clauses) {
		// Before adding new clauses reset not solveable tag
		notSolveable = false;

		try {
			for (final Clause node : clauses) {
				final int[] literals = node.getLiterals();
				solver.addClause(new VecInt(Arrays.copyOf(literals, literals.length)));
			}
		} catch (final ContradictionException e) {
			// throw new RuntimeException(e);
			notSolveable = true; // Tag the CNF as not solvable
		}
	}

	private ISolver createSolver(int size) {
		final ISolver solver = SolverFactory.newDefault();
		solver.setTimeoutMs(1000);
		solver.newVar(size);
		return solver;
	}

	@Override
	public boolean isSatisfiable(int[] literals) throws TimeoutException {
		if (notSolveable) {
			return false;
		}
		final int[] unitClauses = new int[literals.length];
		System.arraycopy(literals, 0, unitClauses, 0, unitClauses.length);

		return solver.isSatisfiable(new VecInt(unitClauses));
	}

	public boolean isSatisfiable(Literal[] literals) throws TimeoutException, UnkownLiteralException {
		if (notSolveable) {
			return false;
		}
		final int[] unitClauses = new int[literals.length];
		int i = 0;
		for (final Literal literal : literals) {
			final Integer value = varToInt.get(literal.var);
			if (value == null) {
				throw new UnkownLiteralException(literal);
			}
			unitClauses[i++] = literal.positive ? value : -value;
		}
		return solver.isSatisfiable(new VecInt(unitClauses));
	}

	@Override
	public void reset() {
		solver.reset();
	}

	@Override
	public void addClause(DeprecatedClause mainClause) {
		final int[] literals = mainClause.literals;

		try {
			solver.addClause(new VecInt(Arrays.copyOf(literals, literals.length)));
		} catch (final ContradictionException e) {
//			throw new RuntimeException(e);
			notSolveable = true; // Tag the CNF as not solvable
		}

	}

}
