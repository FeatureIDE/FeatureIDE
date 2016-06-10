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

import java.util.ArrayList;
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
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

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
	protected final List<int[]> solutionList = new ArrayList<int[]>();
	private ArrayList<IConstr> constraints = new ArrayList<>();

	public BasicSolver(Node cnf, List<IFeature> featureList) {
		this(new SatInstance(cnf, featureList));
	}

	public BasicSolver(SatInstance satInstance) {
		this.satInstance = satInstance;
		final int numberOfVariables = satInstance.getNumberOfVariables();
		this.order = new int[numberOfVariables];
		fixOrder();
		this.assignment = new VecInt(numberOfVariables);
		solver = initSolver();
	}

	public BasicSolver(BasicSolver oldSolver) {
		this.satInstance = oldSolver.satInstance;
		this.order = new int[satInstance.intToVar.length - 1];
		fixOrder();
		this.assignment = new VecInt(0);
		oldSolver.assignment.copyTo(this.assignment);
		solver = initSolver();
	}

	protected Solver<?> initSolver() {
		Solver<?> solver = (Solver<?>) SolverFactory.newDefault();
		solver.setTimeoutMs(1000);
		solver.setDBSimplificationAllowed(false);
		solver.setVerbose(false);
		
		solver.newVar(satInstance.getNumberOfVariables());
		final Node[] cnfChildren = satInstance.getCnf().getChildren();
		solver.setExpectedNumberOfClauses(cnfChildren.length);
		try {
			for (Node node : cnfChildren) {
				final Node[] children = node.getChildren();
				final int[] clause = new int[children.length];
				for (int i = 0; i < children.length; i++) {
					final Literal literal = (Literal) children[i];
					clause[i] = satInstance.getSignedVariable(literal);
				}
				IConstr constraint = solver.addClause(new VecInt(clause));
				constraints.add(constraint);
			}
		} catch (ContradictionException e) {
			Logger.logError(e);
		}
		
		return solver;
	}

	public int[] findModel() {
		return sat() == SatResult.TRUE ? solver.model() : null;
	}

	public IVecInt getAssignmentCopy() {
		final VecInt copy = new VecInt(0);
		assignment.copyTo(copy);
		return copy;
	}

	public void assignmentPop() {
		assignment.pop();
	}

	public void assignmentPush(int x) {
		assignment.push(x);
	}

	public void assignmentClear(int size) {
		assignment.shrinkTo(size);
	}

	public void ensure(int size) {
		assignment.ensure(size);
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

	public Solver<?> getSolver() {
		return solver;
	}

	public SatResult sat() {
		try {
			if (solver.isSatisfiable(assignment, false)) {
				solutionList.add(solver.model());
				return SatResult.TRUE;
			} else {
				return SatResult.FALSE;
			}
		} catch (TimeoutException e) {
			e.printStackTrace();
			return SatResult.TIMEOUT;
		}
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

	@Override
	public void checkAllVariables(int length, Tester t, IMonitor workMonitor) {
		for (int i = 0; i < length; i++) {
			final int varX = t.getNextVariable(i);
			if (varX != 0) {
				assignment.push(varX);
				try {
					if (solver.isSatisfiable(assignment, false)) {
						solutionList.add(solver.model());
						shuffleOrder();
						assignment.pop();
					} else {
						assignment.pop().unsafePush(-varX);
						workMonitor.invoke(-varX);
					}
				} catch (final TimeoutException e) {
					e.printStackTrace();
					assignment.pop();
				}
				workMonitor.step();
			}
		}
	}
	
	@Override
	public void checkAllVariables(int length, Tester t) {
		for (int i = 0; i < length; i++) {
			final int varX = t.getNextVariable(i);
			if (varX != 0) {
				assignment.push(varX);
				try {
					if (solver.isSatisfiable(assignment, false)) {
						solutionList.add(solver.model());
						shuffleOrder();
						assignment.pop();
					} else {
						assignment.pop().unsafePush(-varX);
					}
				} catch (final TimeoutException e) {
					e.printStackTrace();
					assignment.pop();
				}
			}
		}
	}

	@Override
	public int getNumberOfSolutions() {
		return solutionList.size();
	}

	@Override
	public List<int[]> getSolutions() {
		return solutionList;
	}

	public IConstr getConstraint(int i) {
		return constraints.get(i);
	}

}
