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

import java.util.List;
import java.util.Random;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.Semaphore;

import org.prop4j.Node;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.core.Heap;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.NegativeLiteralSelectionStrategy;
import org.sat4j.minisat.orders.PositiveLiteralSelectionStrategy;
import org.sat4j.minisat.orders.RSATPhaseSelectionStrategy;
import org.sat4j.minisat.orders.RandomLiteralSelectionStrategy;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class MultiSolver extends BasicSolver {

	public class Consumer extends Thread {

		private final IVecInt backbone = new VecInt();
		private boolean run = true;
		private final Solver<?> solver;

		public Consumer(Solver<?> solver) {
			this.solver = solver;
		}

		@Override
		public void run() {
			consume();
		}

		public final void consume() {
			try {
				while (run) {
					final Integer var = varQueue.take();
					if (!run) {
						break;
					}
					synchronized (orderLock) {
						switch (curSelectionStrategy) {
						case NEGATIVE:
							solver.setOrder(new VarOrderHeap2(new NegativeLiteralSelectionStrategy(), order, orderLock));
							break;
						case ORG:
							solver.setOrder(new VarOrderHeap(new RSATPhaseSelectionStrategy()));
							break;
						case POSITIVE:
							solver.setOrder(new VarOrderHeap2(new PositiveLiteralSelectionStrategy(), order, orderLock));
							break;
						case RANDOM:
							solver.setOrder(new VarOrderHeap2(new RandomLiteralSelectionStrategy(), order, orderLock));
							break;
						}
					}
					final int index = backbone.size();
					synchronized (assignment) {
						for (int i = index; i < assignment.size(); i++) {
							backbone.push(assignment.get(i));
						}
					}
					backbone.push(var);
					try {
						if (solver.isSatisfiable(backbone, false)) {
							synchronized (solutionList) {
								solutionList.add(solver.model());
							}
							shuffleOrder();
							// handleTrue();
						} else {
							assignmentPush(-var);
							// handleFalse();
						}
					} catch (final TimeoutException e) {
						e.printStackTrace();
						// handleTimeout();
					} finally {
						backbone.pop();
					}
					semaphore.release();
				}
			} catch (final InterruptedException e) {}
		}

		public void stopComsumer() {
			run = false;
			interrupt();
		}

	}

	public static class VarOrderHeap2 extends VarOrderHeap {

		private static final long serialVersionUID = 1L;

		private final Object orderLock;
		private final int[] order;

		public VarOrderHeap2(IPhaseSelectionStrategy strategy, int[] order, Object orderLock) {
			super(strategy);
			this.order = order;
			this.orderLock = orderLock;
		}

		@Override
		public void init() {
			int nlength = lits.nVars() + 1;
			if ((activity == null) || (activity.length < nlength)) {
				activity = new double[nlength];
			}
			phaseStrategy.init(nlength);
			activity[0] = -1;
			heap = new Heap(activity);
			heap.setBounds(nlength);
			nlength--;
			synchronized (orderLock) {
				for (int i = 0; i < nlength; i++) {
					final int x = order[i];
					activity[x] = 0.0;
					if (lits.belongsToPool(x)) {
						heap.insert(x);
					}
				}
			}
		}

	}

	protected static int NUMBER_OF_THREADS = 1;
	static {
		final int processors = Runtime.getRuntime().availableProcessors();
		NUMBER_OF_THREADS = (processors == 1) ? processors : processors >> 1;
	}

	protected final Consumer[] solvers;

	private final Object orderLock = new Object();
	private final BlockingQueue<Integer> varQueue = new LinkedBlockingQueue<>();

	private Semaphore semaphore;

	public MultiSolver(MultiSolver oldSolver) {
		super(oldSolver);
		solvers = new Consumer[oldSolver.solvers.length];
		for (int i = 0; i < solvers.length; i++) {
			final Consumer solver = new Consumer(initSolver());
			solver.solver.setOrder(oldSolver.solvers[i].solver.getOrder());
			solvers[i] = solver;
		}
	}

	public MultiSolver(Node cnf, List<IFeature> featureList) throws ContradictionException {
		this(new SatInstance(cnf, featureList));
	}

	public MultiSolver(SatInstance satInstance) throws ContradictionException {
		super(satInstance);
		solvers = new Consumer[NUMBER_OF_THREADS];
		for (int i = 0; i < solvers.length; i++) {
			solvers[i] = new Consumer(initSolver());
		}
	}

	@Override
	public void assignmentClear(int fromIndex) {
		synchronized (assignment) {
			assignment.shrinkTo(fromIndex);
		}
	}

	@Override
	public void assignmentPop() {
		synchronized (assignment) {
			assignment.pop();
		}
	}

	@Override
	public void assignmentPush(int x) {
		synchronized (assignment) {
			assignment.push(x);
		}
	}

	@Override
	public MultiSolver clone() {
		return new MultiSolver(this);
	}

	@Override
	public void fixOrder() {
		synchronized (order) {
			for (int i = 0; i < order.length; i++) {
				order[i] = i + 1;
			}
		}
	}

	@Override
	public SatResult isSatisfiable() {
		try {
			if (solver.isSatisfiable(assignment, false)) {
				synchronized (solutionList) {
					solutionList.add(solver.model());
				}
				return SatResult.TRUE;
			} else {
				return SatResult.FALSE;
			}
		} catch (final TimeoutException e) {
			e.printStackTrace();
			return SatResult.TIMEOUT;
		}
	}

	@Override
	public void setOrder(List<IFeature> orderList) {
		int i = -1;
		synchronized (orderLock) {
			for (final IFeature feature : orderList) {
				order[++i] = satInstance.varToInt.get(feature.getName());
			}
		}
	}

	private SelectionStrategy curSelectionStrategy = SelectionStrategy.ORG;

	@Override
	public void setSelectionStrategy(SelectionStrategy strategy) {
		super.setSelectionStrategy(strategy);

		synchronized (orderLock) {
			curSelectionStrategy = strategy;
		}
	}

	@Override
	public void shuffleOrder() {
		final Random rnd = new Random();
		synchronized (orderLock) {
			for (int i = order.length - 1; i >= 0; i--) {
				final int index = rnd.nextInt(i + 1);
				final int a = order[index];
				order[index] = order[i];
				order[i] = a;
			}
		}
	}

	@Override
	public int getNumberOfSolutions() {
		synchronized (solutionList) {
			return solutionList.size();
		}
	}

}
