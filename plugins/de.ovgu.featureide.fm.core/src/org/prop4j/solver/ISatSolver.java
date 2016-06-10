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

import java.util.List;

import org.sat4j.minisat.core.Solver;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.IVecInt;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds certain solutions of propositional formulas.
 * 
 * @author Sebastian Krieter
 */
public interface ISatSolver extends Cloneable {

	public static enum SatResult {
		FALSE, TIMEOUT, TRUE
	}

	public static enum SelectionStrategy {
		NEGATIVE, ORG, POSITIVE, RANDOM
	}

	public interface Tester {
		int getNextVariable(int index);
	}

	void assignmentClear(int size);

	void assignmentPop();

	void assignmentPush(int x);

	void checkAllVariables(int length, Tester t);

	void checkAllVariables(int vars, Tester t, IMonitor workMonitor);

	ISatSolver clone();

	int[] findModel();

	void fixOrder();

	IVecInt getAssignmentCopy();

	List<String> getAssignmentString();

	int[] getModel();

	int getNumberOfSolutions();

	SatInstance getSatInstance();

	List<int[]> getSolutions();

	Solver<?> getSolver();

	SatResult sat();

	void setOrder(List<IFeature> orderList);

	void setSelectionStrategy(SelectionStrategy strategy);

	void shuffleOrder();

	IConstr getConstraint(int i);

}
