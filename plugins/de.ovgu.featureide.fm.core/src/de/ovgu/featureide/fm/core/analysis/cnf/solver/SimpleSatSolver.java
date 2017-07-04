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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.Solver;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.IInternalVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

/**
 * Light version of a sat solver with reduced functionality.
 * 
 * @author Sebastian Krieter
 */
public class SimpleSatSolver implements ISimpleSatSolver {

	// XXX: Must be initialized here (is used in ModifiableSatSolver)
	protected final ArrayList<IConstr> constrList = new ArrayList<>();

	protected final CNF satInstance;
	protected final IInternalVariables internalMapping;
	protected final Solver<?> solver;

	public SimpleSatSolver(CNF satInstance) throws RuntimeContradictionException {
		this.satInstance = satInstance;
		this.internalMapping = satInstance.getInternalVariables();
		this.solver = newSolver();
	}

	protected SimpleSatSolver(SimpleSatSolver oldSolver) {
		this.satInstance = oldSolver.satInstance;
		this.internalMapping = oldSolver.internalMapping;
		this.solver = newSolver();
	}

	@Override
	public IConstr addClause(LiteralSet mainClause) throws RuntimeContradictionException {
		return addClauseInternal(solver, mainClause.getLiterals(), 0, mainClause.size());
	}
	
	protected IConstr addClauseInternal(Solver<?> solver, int[] mainClause, int start, int end) throws RuntimeContradictionException {
		try {
			final int[] literals = internalMapping.convertToInternal(mainClause);
			assert checkClauseValidity(literals);
			return solver.addClause(new VecInt(Arrays.copyOfRange(literals, start, end)));
		} catch (ContradictionException e) {
			throw new RuntimeContradictionException(e);
		}
	}

	protected IConstr addClauseInternal(Solver<?> solver, VecInt vec) throws RuntimeContradictionException {
		try {
			return solver.addClause(vec);
		} catch (ContradictionException e) {
			throw new RuntimeContradictionException(e);
		}
	}

	@Override
	public List<IConstr> addClauses(Iterable<? extends LiteralSet> clauses) throws RuntimeContradictionException {
		return addClauses(solver, clauses);
	}

	protected List<IConstr> addClauses(Solver<?> solver, Iterable<? extends LiteralSet> clauses) throws RuntimeContradictionException {
		final ArrayList<IConstr> constrList = new ArrayList<>();
		for (LiteralSet clause : clauses) {
			constrList.add(addClauseInternal(solver, clause.getLiterals(), 0, clause.size()));
		}
		return constrList;
	}

	@Override
	public SimpleSatSolver clone() {
		if (this.getClass() == SimpleSatSolver.class) {
			return new SimpleSatSolver(this);
		} else {
			throw new RuntimeException("Cloning not supported for " + this.getClass().toString());
		}
	}

	@Override
	public CNF getSatInstance() {
		return satInstance;
	}

	@Override
	public int[] getSolution() {
		return internalMapping.convertToOriginal(solver.model());
	}

	@Override
	public SatResult hasSolution() {
		try {
			if (solver.isSatisfiable(false)) {
				return SatResult.TRUE;
			} else {
				return SatResult.FALSE;
			}
		} catch (TimeoutException e) {
			e.printStackTrace();
			return SatResult.TIMEOUT;
		}
	}

	@Override
	public SatResult hasSolution(int... assignment) {
		final int[] unitClauses = new int[assignment.length];
		System.arraycopy(internalMapping.convertToInternal(assignment), 0, unitClauses, 0, unitClauses.length);

		try {
			if (solver.isSatisfiable(new VecInt(unitClauses), false)) {
				return SatResult.TRUE;
			} else {
				return SatResult.FALSE;
			}
		} catch (TimeoutException e) {
			e.printStackTrace();
			return SatResult.TIMEOUT;
		}
	}

	@Override
	public void removeClause(IConstr constr) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void removeLastClause() {
		removeLastClauses(1);
	}

	@Override
	public void removeLastClauses(int numberOfClauses) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void reset() {
		solver.reset();
	}

	private boolean checkClauseValidity(final int[] literals) {
		for (int i = 0; i < literals.length; i++) {
			final int l = literals[i];
			if (l == 0 || Math.abs(l) > satInstance.getVariables().maxVariableID()) {
				return false;
			}
		}
		return true;
	}

	protected final Solver<?> newSolver() throws RuntimeContradictionException {
		final Solver<?> solver = createSolver();
		configureSolver(solver);
		initSolver(solver);
		return solver;
	}

	/**
	 * Creates the Sat4J solver instance.
	 */
	protected Solver<?> createSolver() {
		return (Solver<?>) SolverFactory.newDefault();
	}

	/**
	 * Set several options for the Sat4J solver instance.
	 */
	protected void configureSolver(Solver<?> solver) {
		solver.setTimeoutMs(1000);
		solver.setDBSimplificationAllowed(true);
		solver.setVerbose(false);
	}

	/**
	 * Add clauses to the solver.
	 * Initializes the order instance.
	 */
	protected void initSolver(Solver<?> solver) throws RuntimeContradictionException {
		final int size = satInstance.getVariables().size();
		final List<LiteralSet> clauses = satInstance.getClauses();
		if (!clauses.isEmpty()) {
			solver.setExpectedNumberOfClauses(clauses.size() + 1);
			addClauses(solver, clauses);
		}
		if (size > 0) {
			final VecInt pseudoClause = new VecInt(size + 1);
			for (int i = 1; i <= size; i++) {
				pseudoClause.push(i);
			}
			pseudoClause.push(-1);
			try {
				solver.addClause(pseudoClause);
			} catch (ContradictionException e) {
				throw new RuntimeContradictionException(e);
			}
		}
		solver.getOrder().init();
	}

	public void setTimeout(int timeout) {
		solver.setTimeout(timeout);
	}

}