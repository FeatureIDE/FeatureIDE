/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.List;
import java.util.Random;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.base.util.RingList;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public interface ISatSolver extends ISimpleSatSolver {

	public static final int MAX_SOLUTION_BUFFER = 1000;

	public static enum SelectionStrategy {
		NEGATIVE, ORG, POSITIVE, RANDOM, UNIFORM_RANDOM, FIXED
	}

	RingList<int[]> getSolutionList();

	void useSolutionList(int size);

	@Override
	ISatSolver clone();

	int[] findSolution();

	int[] getOrder();

	void setOrder(int[] order);

	void setOrderFix();

	void shuffleOrder();

	void shuffleOrder(Random rnd);

	SelectionStrategy getSelectionStrategy();

	void setSelectionStrategy(SelectionStrategy strategy);

	void setSelectionStrategy(int[] model, boolean min);

	void setSelectionStrategy(List<LiteralSet> sample);

	void assignmentPop();

	void assignmentPush(int x);

	void assignmentPushAll(int[] literals);

	void assignmentReplaceLast(int x);

	void assignmentClear(int size);

	void asignmentEnsure(int size);

	int assignmentGet(int i);

	void assignmentDelete(int i);

	void assignmentSet(int index, int var);

	int[] getAssignmentArray();

	int[] getAssignmentArray(int from);

	int[] getAssignmentArray(int from, int to);

	int getAssignmentSize();

	int[] getContradictoryAssignment();

	boolean isGlobalTimeout();

	void setGlobalTimeout(boolean globalTimeout);

}
