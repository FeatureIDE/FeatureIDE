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

import java.util.Arrays;
import java.util.List;
import java.util.Random;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IConstr;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.IInternalVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.base.util.RingList;

/**
 * Sat solver with advanced support.
 *
 * @author Sebastian Krieter
 */
public class EmptySatSolver implements ISatSolver {

	private final CNF satInstance;
	protected final VecInt assignment;

	public EmptySatSolver(CNF satInstance) throws RuntimeContradictionException {
		this.satInstance = satInstance;
		assignment = new VecInt(satInstance.getVariables().size());
	}

	protected EmptySatSolver(EmptySatSolver oldSolver) {
		satInstance = oldSolver.satInstance;
		assignment = new VecInt(0);
		oldSolver.assignment.copyTo(assignment);
	}

	@Override
	public void assignmentClear(int size) {
		assignment.shrinkTo(size);
	}

	@Override
	public void asignmentEnsure(int size) {
		assignment.ensure(size);
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
	public void assignmentPushAll(int[] x) {
		assignment.pushAll(new VecInt(x));
	}

	@Override
	public void assignmentReplaceLast(int x) {
		assignment.pop().unsafePush(x);
	}

	@Override
	public void assignmentDelete(int i) {
		assignment.delete(i);
	}

	@Override
	public void assignmentSet(int index, int var) {
		assignment.set(index, var);
	}

	@Override
	public int getAssignmentSize() {
		return assignment.size();
	}

	@Override
	public EmptySatSolver clone() {
		if (this.getClass() == EmptySatSolver.class) {
			return new EmptySatSolver(this);
		} else {
			throw new RuntimeException("Cloning not supported for " + this.getClass().toString());
		}
	}

	@Override
	public int[] findSolution() {
		return null;
	}

	@Override
	public int[] getAssignmentArray() {
		return Arrays.copyOf(assignment.toArray(), assignment.size());
	}

	@Override
	public int[] getAssignmentArray(int from) {
		return Arrays.copyOfRange(assignment.toArray(), from, assignment.size());
	}

	@Override
	public int[] getAssignmentArray(int from, int to) {
		return Arrays.copyOfRange(assignment.toArray(), from, to);
	}

	@Override
	public int assignmentGet(int i) {
		return assignment.get(i);
	}

	@Override
	public int[] getOrder() {
		return null;
	}

	@Override
	public SelectionStrategy getSelectionStrategy() {
		return null;
	}

	@Override
	public RingList<int[]> getSolutionList() {
		return null;
	}

	@Override
	public SatResult hasSolution() {
		return null;
	}

	@Override
	public SatResult hasSolution(int... assignment) {
		return null;
	}

	@Override
	public int[] getContradictoryAssignment() {
		return null;
	}

	@Override
	public void setOrder(int[] order) {}

	@Override
	public void setOrderFix() {}

	@Override
	public void shuffleOrder() {}

	@Override
	public void shuffleOrder(Random rnd) {}

	@Override
	public void setSelectionStrategy(SelectionStrategy strategy) {}

	@Override
	public void setSelectionStrategy(int[] model, boolean min) {}

	@Override
	public void useSolutionList(int size) {}

	@Override
	public boolean isGlobalTimeout() {
		return false;
	}

	@Override
	public void setGlobalTimeout(boolean globalTimeout) {}

	@Override
	public IConstr addClause(LiteralSet mainClause) throws RuntimeContradictionException {
		return null;
	}

	@Override
	public IConstr addInternalClause(LiteralSet mainClause) throws RuntimeContradictionException {
		return null;
	}

	@Override
	public List<IConstr> addClauses(Iterable<? extends LiteralSet> clauses) throws RuntimeContradictionException {
		return null;
	}

	@Override
	public List<IConstr> addInternalClauses(Iterable<? extends LiteralSet> clauses) throws RuntimeContradictionException {
		return null;
	}

	@Override
	public void removeClause(IConstr constr) {}

	@Override
	public void removeLastClause() {}

	@Override
	public void removeLastClauses(int numberOfClauses) {}

	@Override
	public int[] getSolution() {
		return null;
	}

	@Override
	public CNF getSatInstance() {
		return satInstance;
	}

	@Override
	public void reset() {}

	@Override
	public void setTimeout(int timeout) {

	}

	@Override
	public int[] getInternalSolution() {
		return null;
	}

	@Override
	public IInternalVariables getInternalMapping() {
		return null;
	}

}
