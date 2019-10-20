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
package org.prop4j.analyses.impl.general.sat;

import java.util.ArrayList;
import java.util.List;

import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.impl.SolverManager;
import org.prop4j.solver.impl.SolverUtils;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features using filtering. We use intermediate solution as filter to reduce the overall satisfiability requests.
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class CoreDeadAnalysis extends AbstractSatSolverAnalysis<LiteralSet> {

	public CoreDeadAnalysis(ISatProblem problem) {
		super(problem);
	}

	public CoreDeadAnalysis(ISatSolver solver) {
		super(solver);
	}

	@Override
	public LiteralSet analyze(IMonitor<LiteralSet> monitor) {
		final List<Integer> features = new ArrayList<>();
		getSolver().isSatisfiable();
		final int[] model1 = SolverUtils.getIntModel(getSolver().getSolution());
		for (int i = 0; i < model1.length; i++) {
			final int varX = model1[i];
			if (varX != 0) {
				try {
					getSolver().push(getSolver().getProblem().getVariableAsNode(-varX));
				} catch (final ContradictionException e) {
					// Unsatisfiable => dead or core feature
					try {
						getSolver().push(getSolver().getProblem().getVariableAsNode(varX));
					} catch (final ContradictionException e1) {
						// Should not be thrown
					}
					// Memorize varX as core/dead feature
					features.add(varX);
				}
				switch (getSolver().isSatisfiable()) {
				case FALSE:
					// Unsatisfiable => dead or core feature
					getSolver().pop();
					try {
						getSolver().push(getSolver().getProblem().getVariableAsNode(varX));
					} catch (final ContradictionException e) {
						FMCorePlugin.getDefault().logError(e);
					}
					// Memorize varX as core/dead feature
					features.add(varX);
					break;
				case TIMEOUT:
					getSolver().pop();
					break;
				case TRUE:
					getSolver().pop();
					SolverUtils.updateModel(model1, SolverUtils.getIntModel(getSolver().getSolution()));
					break;
				}
			}
		}
		final int[] result = new int[features.size()];
		for (int i = 0; i < result.length; i++) {
			result[i] = features.get(i);
		}
		return new LiteralSet(result);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.GeneralSolverAnalysis#analyze(de.ovgu.featureide.fm.core.job.monitor.IMonitor)
	 */
	@Override
	public ISatSolver initSolver(ISatProblem problem) {
		if (solver == null) {
			// Create new solver
			solver = SolverManager.getSelectedFeatureAttributeSolverFactory().getAnalysisSolver(problem);
		}
		return solver;
	}
}
