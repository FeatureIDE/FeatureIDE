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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.prop4j.Node;
import org.prop4j.analyses.AbstractSolverAnalysisFactory;
import org.prop4j.analyses.GeneralSolverAnalysis;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatResult;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.impl.SatProblem;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * Finds constraints that are unsatisfiable.
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class ConstraintsUnsatisfiableAnalysis extends GeneralSolverAnalysis<Map<IConstraint, ConstraintAttribute>> {

	public ConstraintsUnsatisfiableAnalysis(ISolver solver, AbstractSolverAnalysisFactory factory) {
		super(solver);
		this.factory = factory;
	}

	private final AbstractSolverAnalysisFactory factory;
	private List<IConstraint> constraints;

	@Override
	public Map<IConstraint, ConstraintAttribute> analyze(IMonitor monitor) {
		if ((constraints == null) || constraints.isEmpty()) {
			return new HashMap<>();
		}
		final Map<IConstraint, ConstraintAttribute> map = new HashMap<>();

		monitor.checkCancel();

		for (final IConstraint constraint : constraints) {
			final Node cnf = constraint.getNode().toRegularCNF();

			boolean satisfiable;
			try {
				solver.push(cnf);
				satisfiable = solver.isSatisfiable() == ISatResult.TRUE;

				if (!satisfiable) {
					solver.pop();
					if (checkConstraintContradiction(cnf)) {
						map.put(constraint, ConstraintAttribute.UNSATISFIABLE);
					} else {
						map.put(constraint, ConstraintAttribute.VOID_MODEL);
					}
				}
			} catch (final ContradictionException e) {
				satisfiable = false;
				map.put(constraint, ConstraintAttribute.UNSATISFIABLE);
			}

			monitor.checkCancel();
		}
		return map;
	}

	public List<IConstraint> getConstraints() {
		return constraints;
	}

	public void setConstraints(List<IConstraint> constraints) {
		this.constraints = constraints;
	}

	private boolean checkConstraintContradiction(Node constraintNode) {
		final ISatProblem problem = new SatProblem(constraintNode);
		final org.prop4j.analyses.impl.general.ValidAnalysis validAnalysis =
			(org.prop4j.analyses.impl.general.ValidAnalysis) factory.getAnalysis(org.prop4j.analyses.impl.general.ValidAnalysis.class, problem);
		return LongRunningWrapper.runMethod(validAnalysis, new NullMonitor()) == null;
	}
}
