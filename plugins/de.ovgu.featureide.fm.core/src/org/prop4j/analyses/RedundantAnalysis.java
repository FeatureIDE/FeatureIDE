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
package org.prop4j.analyses;

import java.util.ArrayList;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.solver.ISatSolver;
import org.sat4j.core.VecInt;
import org.sat4j.specs.IConstr;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds atomic sets.
 * 
 * @author Sebastian Krieter
 */
public class RedundantAnalysis extends AbstractAnalysis<List<Integer>> {

	private final int[] nodeIndex;

	public RedundantAnalysis(ISatSolver solver, int[] nodeIndex) {
		super(solver);
		this.nodeIndex = nodeIndex;
	}

	@Override
	public List<Integer> execute(IMonitor monitor) throws Exception {
		final List<Integer> redundantConstraints = new ArrayList<>();
		final Node[] children2 = solver.getSatInstance().getCnf().getChildren();
		
		for (int index : nodeIndex) {
			final IConstr constraint = solver.getConstraint(index);
			if (constraint == null) {
				redundantConstraints.add(index);
				continue;
			}
			solver.getSolver().removeConstr(constraint);
			
			final Node[] children = children2[index].getChildren();
			final int[] clause = new int[children.length];
			for (int i = 0; i < children.length; i++) {
				final Literal literal = (Literal) children[i];
				int var = solver.getSatInstance().getSignedVariable(literal);
				clause[i] = var;
				solver.assignmentPush(-var);
			}
			switch (solver.sat()) {
				case FALSE:
					redundantConstraints.add(index);
					break;
				case TIMEOUT:
				case TRUE:
					solver.getSolver().addClause(new VecInt(clause));
					break;
				default:
					break;
			}
			solver.assignmentClear(0);
			
		}

		return redundantConstraints;
	}

}
