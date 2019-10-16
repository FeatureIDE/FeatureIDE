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

import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.analyses.AbstractSatSolverAnalysis;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.impl.SolverManager;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds redundancies by removing single constraints.
 *
 * @author Joshua Sprey
 * @author Sebastian Krieter
 */
public class RedundancyAnalysis extends AbstractSatSolverAnalysis<List<IConstraint>> {

	private final List<IConstraint> constraints;

	public RedundancyAnalysis(ISatProblem instance, List<IConstraint> constraints) {
		super(instance);
		this.constraints = constraints;
	}

	public RedundancyAnalysis(ISatSolver solver, List<IConstraint> constraints) {
		super(solver);
		this.constraints = constraints;
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

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.GeneralSolverAnalysis#analyze(de.ovgu.featureide.fm.core.job.monitor.IMonitor)
	 */
	@Override
	protected List<IConstraint> analyze(IMonitor<List<IConstraint>> monitor) throws Exception {
		if ((constraints == null) || constraints.isEmpty()) {
			return new ArrayList<IConstraint>();
		}
		final List<IConstraint> resultList = new ArrayList<>();
		final List<Node> cnfNodes = new ArrayList<>();
		final List<Node> cnfNegatedNodes = new ArrayList<>();

//		// Sort the constraint by the length of their children
//		Collections.sort(constraintsLocal, new Comparator<IConstraint>() {
//
//			@Override
//			public int compare(IConstraint o1, IConstraint o2) {
//				final int o1Childs = o1.getNode().toRegularCNF().getChildren().length;
//				final int o2Childs = o2.getNode().toRegularCNF().getChildren().length;
//				if (o1Childs == o2Childs) {
//					return 0;
//				} else if (o1Childs > o2Childs) {
//					return 1;
//				} else {
//					return -1;
//				}
//			}
//		});

		for (int i = 0; i < constraints.size(); i++) {
			final Node cnf = constraints.get(i).getNode().toRegularCNF();
			cnfNodes.add(cnf);
			cnfNegatedNodes.add(new Not(cnf).toRegularCNF());
			// Skip first constraint because we want to check it first and dont need to remove it later.
			if (i > 0) {
				try {
					solver.push(cnf);
				} catch (final ContradictionException e) {}
			}
		}

		monitor.checkCancel();

		for (int j = 0; j < constraints.size(); j++) {
			boolean redundant = false;
			// Negated constraint contains multiple clauses. The solver can handle cnf and nodes. We only need to pop one time.
			final Node negatedConstraint = cnfNegatedNodes.get(j);
			try {
				solver.push(negatedConstraint);
			} catch (final ContradictionException e) {
				// Unsatisfiable => redundant
				redundant = true;
				solver.pop();
			}
			if (!redundant) {
				switch (solver.isSatisfiable()) {
				case TRUE:
					solver.pop();
					break;
				case TIMEOUT:
					reportTimeout();
					solver.pop();
					break;
				case FALSE:
					redundant = true;
					solver.pop();
					break;
				default:
					break;
				}
			}

			// Now the solver does no longer contain the checked constraint but only with index >j
			try {
				// Remove all until index j
				solver.pop(constraints.size() - 1 - j);

				// Add checked constraint to solver if not redundant
				if (redundant) {
					// Don't add the redundant constraint to the solver
					resultList.add(constraints.get(j));
				} else {
					solver.push(cnfNodes.get(j));
				}

				// Add remaining constraints (index [j+2]-[n]) and skip the next checked constraint (index [j+1])
				// because it will be added as negation in the next iteration
				for (int j2 = j + 2; j2 < constraints.size(); j2++) {
					solver.push(cnfNodes.get(j2));
				}
			} catch (final ContradictionException e1) {}

			monitor.checkCancel();
		}

		return resultList;
	}

}
