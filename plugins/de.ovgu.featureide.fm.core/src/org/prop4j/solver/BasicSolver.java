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
import java.util.Random;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.Heap;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.NegativeLiteralSelectionStrategy;
import org.sat4j.minisat.orders.PositiveLiteralSelectionStrategy;
import org.sat4j.minisat.orders.RandomLiteralSelectionStrategy;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Finds certain solutions of propositional formulas.
 * 
 * @author Sebastian Krieter
 */
public class BasicSolver implements Cloneable {

	public static enum SatResult {
		TRUE, FALSE, TIMEOUT
	}

	public static enum SelectionStrategy {
		ORG, POSITIVE, NEGATIVE, RANDOM
	}

	private class VarOrderHeap2 extends VarOrderHeap {

		private static final long serialVersionUID = 1L;

		public VarOrderHeap2(IPhaseSelectionStrategy strategy) {
			super(strategy);
		}

		@Override
		public void init() {
			int nlength = this.lits.nVars() + 1;
			if (this.activity == null || this.activity.length < nlength) {
				this.activity = new double[nlength];
			}
			this.phaseStrategy.init(nlength);
			this.activity[0] = -1;
			this.heap = new Heap(this.activity);
			this.heap.setBounds(nlength);
			nlength--;
			for (int i = 0; i < nlength; i++) {
				final int x = order[i];
				this.activity[x] = 0.0;
				if (this.lits.belongsToPool(x)) {
					this.heap.insert(x);
				}
			}
		}
	}

	protected final SatInstance satInstance;
	protected final Solver<?> solver;
	protected final IOrder orgSolverOrder;
	protected final int[] order;
	protected final VecInt assignment;

	protected boolean keepHot = false;

	public BasicSolver(SatInstance satInstance) throws ContradictionException {
		this.satInstance = satInstance;
		this.order = new int[satInstance.intToVar.length - 1];
		this.assignment = new VecInt();

		solver = initSolver();
		addVariables();

		orgSolverOrder = solver.getOrder();
		orgSolverOrder.init();
	}

	protected BasicSolver(BasicSolver oldSolver) {
		this.satInstance = oldSolver.satInstance;
		this.order = new int[satInstance.intToVar.length - 1];
		this.assignment = new VecInt(0);
		oldSolver.assignment.copyTo(this.assignment);

		solver = initSolver();
		try {
			addVariables();
		} catch (ContradictionException e) {
			FMCorePlugin.getDefault().logError(e);
			throw new RuntimeException();
		}

		orgSolverOrder = solver.getOrder();
	}

	private void addVariables() throws ContradictionException {
		solver.newVar(satInstance.getNumberOfVariables());
		solver.setExpectedNumberOfClauses(satInstance.getCnf().getChildren().length);
		addCNF(satInstance.getCnf().getChildren());
		fixOrder();
	}

	protected Solver<?> initSolver() {
		final Solver<?> solver = (Solver<?>) SolverFactory.newDefault();
		solver.setTimeoutMs(1000);
		solver.setDBSimplificationAllowed(true);
		solver.setVerbose(false);
		return solver;
	}

	public List<IConstr> addClauses(Node constraint) throws ContradictionException {
		return addCNF(constraint.getChildren());
	}

	protected List<IConstr> addCNF(final Node[] cnfChildren) throws ContradictionException {
		final List<IConstr> result = new LinkedList<>();
		for (Node node : cnfChildren) {
			final Node[] children = node.getChildren();
			final int[] clause = new int[children.length];
			for (int i = 0; i < children.length; i++) {
				final Literal literal = (Literal) children[i];
				clause[i] = satInstance.getSignedVariable(literal);
			}
			result.add(solver.addClause(new VecInt(clause)));
		}
		return result;
	}

	public int[] findModel() {
		return isSatisfiable() == SatResult.TRUE ? solver.model() : null;
	}

	public IVecInt getAssignment() {
		return assignment;
	}

	public List<String> getAssignmentString() {
		return satInstance.convertToString(assignment);
	}

	public int[] getModel() {
		return solver.model();
	}

	public SatInstance getSatInstance() {
		return satInstance;
	}

	public Solver<?> getInternalSolver() {
		return solver;
	}

	public SatResult isSatisfiable() {
		try {
			return (solver.isSatisfiable(assignment, false)) ? SatResult.TRUE : SatResult.FALSE;
		} catch (TimeoutException e) {
			e.printStackTrace();
			return SatResult.TIMEOUT;
		}
	}

	public boolean isKeepHot() {
		return keepHot;
	}

	public void setKeepHot(boolean keepHot) {
		this.keepHot = keepHot;
		solver.setKeepSolverHot(keepHot);
	}

	public void setOrder(List<IFeature> orderList) {
		int i = -1;
		for (IFeature feature : orderList) {
			order[++i] = satInstance.varToInt.get(feature.getName());
		}
	}

	public void setSelectionStrategy(SelectionStrategy strategy) {
		switch (strategy) {
		case NEGATIVE:
			final VarOrderHeap2 negativeHeap = new VarOrderHeap2(new NegativeLiteralSelectionStrategy());
			solver.setOrder(negativeHeap);
			if (keepHot) {
				negativeHeap.init();
			}
			break;
		case ORG:
			solver.setOrder(orgSolverOrder);
			if (keepHot) {
				orgSolverOrder.init();
			}
			break;
		case POSITIVE:
			final VarOrderHeap2 positiveHeap = new VarOrderHeap2(new PositiveLiteralSelectionStrategy());
			solver.setOrder(positiveHeap);
			if (keepHot) {
				positiveHeap.init();
			}
			break;
		case RANDOM:
			final VarOrderHeap2 randomHeap = new VarOrderHeap2(new RandomLiteralSelectionStrategy());
			solver.setOrder(randomHeap);
			if (keepHot) {
				randomHeap.init();
			}
			break;
		default:
			break;
		}
	}

	public void shuffleOrder() {
		final Random rnd = new Random();
		for (int i = order.length - 1; i >= 0; i--) {
			final int index = rnd.nextInt(i + 1);
			final int a = order[index];
			order[index] = order[i];
			order[i] = a;
		}
	}

	public void fixOrder() {
		for (int i = 0; i < order.length; i++) {
			order[i] = i + 1;
		}
	}

	public BasicSolver clone() {
		return new BasicSolver(this);
	}

}
