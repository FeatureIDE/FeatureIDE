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
package org.prop4j.analyses.impl.general;

import java.util.ArrayList;
import java.util.List;

import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.analyses.AbstractSolverAnalysisFactory;
import org.prop4j.analyses.GeneralSolverAnalysis;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.impl.SatProblem;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Checks every constraint of redundancy. Requires no problem.
 *
 * @author Joshua Sprey
 */
public class TautologicalConstraintAnalysis extends GeneralSolverAnalysis<List<IConstraint>> {

	private List<IConstraint> allConstraints;
	private final AbstractSolverAnalysisFactory factory;

	public TautologicalConstraintAnalysis(ISolver solver, AbstractSolverAnalysisFactory factory) {
		super(solver);
		this.factory = factory;
	}

	public void init(List<IConstraint> allConstraints) {
		this.allConstraints = allConstraints;

	}

	@Override
	public List<IConstraint> analyze(IMonitor monitor) {
		final List<IConstraint> result = new ArrayList<>();

		for (final IConstraint iConstraint : allConstraints) {
			final Node negated = new Not(iConstraint.getNode()).toRegularCNF();

			final long timeEdit = System.currentTimeMillis();
			final ValidAnalysis analysis = (ValidAnalysis) factory.getAnalysis(ValidAnalysis.class, new SatProblem(negated));
			editTime += (System.currentTimeMillis() - timeEdit);
			if (analysis == null) {
				// Is tautology
				result.add(iConstraint);
				continue;
			}
			final long time = System.currentTimeMillis();
			if (LongRunningWrapper.runMethod(analysis) == null) {
				// Is tautology
				result.add(iConstraint);
			}
			solveTime += (System.currentTimeMillis() - time);
		}
		return result;
	}

}
