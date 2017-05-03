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

import java.util.Arrays;

import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SatResult;
import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;
import org.sat4j.specs.IVecInt;

import de.ovgu.featureide.fm.core.conf.IFeatureGraph2;
import de.ovgu.featureide.fm.core.conf.IFeatureGraph2.ITraverser;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds implied manual defined variables.
 * 
 * @author Sebastian Krieter
 */
public class DecisionPropagation2AnalysisMIG extends AbstractAnalysis<int[]> {

	private final ITraverser traverser;

	public DecisionPropagation2AnalysisMIG(ISatSolver solver, IFeatureGraph2 featureGraph) {
		super(solver);
		this.traverser = featureGraph.traverse();
	}

	public DecisionPropagation2AnalysisMIG(SatInstance satInstance, IFeatureGraph2 featureGraph) {
		super(satInstance);
		this.traverser = featureGraph.traverse();
	}

	public int[] analyze(IMonitor monitor) throws Exception {
		final int[] modelForDefinedVariables = new int[solver.getSatInstance().getNumberOfVariables()];
		final VecInt result = new VecInt();

		final IVecInt assignment = solver.getAssignment();
		for (int i = 0; i < assignment.size(); i++) {
			Arrays.fill(modelForDefinedVariables, 0);
			for (int j = 0; j < assignment.size(); j++) {
				if (i != j) {
					final int var = assignment.get(j);
					modelForDefinedVariables[Math.abs(var) - 1] = var;
				}
			}
			final int oLiteral = assumptions[i];

			traverser.init(modelForDefinedVariables);
			traverser.traverseDefined(Arrays.copyOf(assignment.toArray(), assignment.size()));

			if (modelForDefinedVariables[Math.abs(oLiteral) - 1] != 0) {
				result.push(oLiteral);
				assignment.delete(i--);
			} else {
				final VecInt v = traverser.getRelevantVariables();
				if (v.contains(oLiteral)) {
					assignment.set(i, -oLiteral);
					final SatResult satResult = solver.isSatisfiable();
					switch (satResult) {
					case FALSE:
						result.push(oLiteral);
						assignment.delete(i--);
						break;
					case TIMEOUT:
					case TRUE:
						assignment.set(i, oLiteral);
						break;
					default:
						throw new AssertionError(satResult);
					}
				}
			}
		}
		return Arrays.copyOf(result.toArray(), result.size());
	}

}
