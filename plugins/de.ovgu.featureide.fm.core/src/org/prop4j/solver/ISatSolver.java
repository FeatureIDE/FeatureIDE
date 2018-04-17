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

import org.prop4j.Node;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.util.RingList;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public interface ISatSolver extends Cloneable {

	public static final int DEFAULT_TIMEOUT = 1000;
	public static final int MAX_SOLUTION_BUFFER = 1000;

	public static enum SatResult {
		FALSE, TIMEOUT, TRUE
	}

	public static enum SelectionStrategy {
		NEGATIVE, ORG, POSITIVE, RANDOM
	}

	void assignmentClear(int size);

	void assignmentPop();

	void assignmentPush(int x);

	void assignmentReplaceLast(int x);

	ISatSolver clone();

	int[] findModel();

	void fixOrder();

	IVecInt getAssignment();

	int[] getAssignmentArray(int from, int to);

	int[] getModel();

	int getNumberOfSolutions();

	SatInstance getSatInstance();

	RingList<int[]> getSolutionList();

	void initSolutionList(int size);

	ISolver getInternalSolver();

	SatResult isSatisfiable();

	void setOrder(List<IFeature> orderList);

	void setSelectionStrategy(SelectionStrategy strategy);

	void shuffleOrder();

	int[] getOrder();

	List<IConstr> addClauses(Node constraint) throws ContradictionException;

	boolean getGlobalTimeout();

	void setGlobalTimeout(boolean globalTimeout);

}
