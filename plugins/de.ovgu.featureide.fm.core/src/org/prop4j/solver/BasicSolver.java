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
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.NegativeLiteralSelectionStrategy;
import org.sat4j.minisat.orders.PositiveLiteralSelectionStrategy;
import org.sat4j.minisat.orders.RSATPhaseSelectionStrategy;
import org.sat4j.minisat.orders.RandomLiteralSelectionStrategy;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.util.RingList;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class BasicSolver implements ISatSolver {

	protected final SatInstance satInstance;
	protected final Solver<?> solver;
	protected final int[] order;
	protected final VecInt assignment;
	protected RingList<int[]> solutionList = null;
	protected boolean globalTimeout = false;

	protected boolean timeoutOccured = false;

	public BasicSolver(SatInstance satInstance) throws ContradictionException {
		this.satInstance = satInstance;
		final int numberOfVariables = satInstance.getNumberOfVariables();
		order = new int[numberOfVariables];
		assignment = new VecInt(numberOfVariables);

		solver = initSolver();
		addVariables();
	}

	protected BasicSolver(BasicSolver oldSolver) {
		satInstance = oldSolver.satInstance;
		order = new int[satInstance.intToVar.length - 1];
		assignment = new VecInt(0);
		oldSolver.assignment.copyTo(assignment);

		solver = initSolver();
		try {
			addVariables();
		} catch (final ContradictionException e) {
			Logger.logError(e);
			throw new RuntimeException();
		}
	}

	private void addVariables() throws ContradictionException {
		final int size = satInstance.getNumberOfVariables();
		if (size > 0) {
			solver.newVar(size);
			solver.setExpectedNumberOfClauses(satInstance.getCnf().getChildren().length + 1);
			addCNF(satInstance.getCnf().getChildren());
			final VecInt pseudoClause = new VecInt(size + 1);
			for (int i = 1; i <= size; i++) {
				pseudoClause.push(i);
			}
			pseudoClause.push(-1);
			solver.addClause(pseudoClause);
		}
		fixOrder();
		solver.getOrder().init();
	}

	protected Solver<?> initSolver() {
		final Solver<?> solver = (Solver<?>) SolverFactory.newDefault();
		solver.setTimeoutMs(DEFAULT_TIMEOUT);
		solver.setDBSimplificationAllowed(true);
		solver.setVerbose(false);
		return solver;
	}

	@Override
	public List<IConstr> addClauses(Node constraint) throws ContradictionException {
		return addCNF(constraint.getChildren());
	}

	protected List<IConstr> addCNF(final Node[] cnfChildren) throws ContradictionException {
		final List<IConstr> result = new ArrayList<>(cnfChildren.length);
		for (final Node node : cnfChildren) {
			result.add(addClause(node));
		}
		return result;
	}

	protected IConstr addClause(final Node node) throws ContradictionException {
		final Node[] children = node.getChildren();
		final int[] clause = new int[children.length];
		for (int i = 0; i < children.length; i++) {
			final Literal literal = (Literal) children[i];
			clause[i] = satInstance.getSignedVariable(literal);
		}
		return solver.addClause(new VecInt(clause));
	}

	@Override
	public int[] findModel() {
		return isSatisfiable() == SatResult.TRUE ? solver.model() : null;
	}

	@Override
	public void assignmentPop() {
		assignment.pop();
	}

	@Override
	public void assignmentPush(int x) {
		assignment.push(x);
	}

	@Override
	public void assignmentClear(int size) {
		assignment.shrinkTo(size);
	}

	@Override
	public int[] getModel() {
		return solver.model();
	}

	@Override
	public SatInstance getSatInstance() {
		return satInstance;
	}

	@Override
	public ISolver getInternalSolver() {
		return solver;
	}

	@Override
	public SatResult isSatisfiable() {
		try {
			if (solver.isSatisfiable(assignment, globalTimeout)) {
				if (solutionList != null) {
					solutionList.add(solver.model());
				}
				return SatResult.TRUE;
			} else {
				return SatResult.FALSE;
			}
		} catch (final TimeoutException e) {
			timeoutOccured = true;
			return SatResult.TIMEOUT;
		}
	}

	@Override
	public void setOrder(List<IFeature> orderList) {
		int i = -1;
		for (final IFeature feature : orderList) {
			order[++i] = satInstance.varToInt.get(feature.getName());
		}
	}

	@Override
	public int[] getOrder() {
		return order;
	}

	@Override
	public void setSelectionStrategy(SelectionStrategy strategy) {
		switch (strategy) {
		case NEGATIVE:
			solver.setOrder(new VarOrderHeap2(new NegativeLiteralSelectionStrategy(), order));
			break;
		case ORG:
			solver.setOrder(new VarOrderHeap(new RSATPhaseSelectionStrategy()));
			break;
		case POSITIVE:
			solver.setOrder(new VarOrderHeap2(new PositiveLiteralSelectionStrategy(), order));
			break;
		case RANDOM:
			solver.setOrder(new VarOrderHeap2(new RandomLiteralSelectionStrategy(), order));
			break;
		default:
			break;
		}
	}

	@Override
	public void shuffleOrder() {
		final Random rnd = new Random();
		for (int i = order.length - 1; i >= 0; i--) {
			final int index = rnd.nextInt(i + 1);
			final int a = order[index];
			order[index] = order[i];
			order[i] = a;
		}
	}

	@Override
	public void fixOrder() {
		for (int i = 0; i < order.length; i++) {
			order[i] = i + 1;
		}
	}

	@Override
	public boolean getGlobalTimeout() {
		return globalTimeout;
	}

	@Override
	public void setGlobalTimeout(boolean globalTimeout) {
		this.globalTimeout = globalTimeout;
	}

	public boolean hasTimeoutOccured() {
		return timeoutOccured;
	}

	public void resetTimeoutOccured() {
		timeoutOccured = false;
	}

	@Override
	public BasicSolver clone() {
		return new BasicSolver(this);
	}

	@Override
	public int getNumberOfSolutions() {
		if (solutionList == null) {
			return 0;
		}
		return solutionList.size();
	}

	@Override
	public RingList<int[]> getSolutionList() {
		return solutionList;
	}

	@Override
	public void assignmentReplaceLast(int x) {
		assignment.pop().unsafePush(x);
	}

	@Override
	public IVecInt getAssignment() {
		return assignment;
	}

	@Override
	public int[] getAssignmentArray(int from, int to) {
		return Arrays.copyOfRange(assignment.toArray(), from, to);
	}

	@Override
	public void initSolutionList(int size) {
		solutionList = new RingList<>(size);
	}

}
