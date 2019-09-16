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
package org.prop4j.analyses.impl.generalCopy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.analyses.AbstractSolverAnalysisFactory;
import org.prop4j.analyses.GeneralSolverAnalysis;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISolver;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds redundant constraints.
 *
 * @author Joshua Sprey
 */
public class RedundantConstraintAnalysis extends GeneralSolverAnalysis<Map<IConstraint, ConstraintAttribute>> {

	public RedundantConstraintAnalysis(ISolver solver, AbstractSolverAnalysisFactory factory) {
		super(solver);
		this.factory = factory;
	}

	AbstractSolverAnalysisFactory factory;
	private List<IConstraint> constraints;

	@Override
	public Map<IConstraint, ConstraintAttribute> analyze(IMonitor monitor) {
		if ((constraints == null) || constraints.isEmpty()) {
			return new HashMap<>();
		}
		final Map<IConstraint, ConstraintAttribute> map = new HashMap<>();
		final List<Node> cnfNodes = new ArrayList<>();
		final List<IConstraint> constraintsLocal = new ArrayList<>(3);
		for (final IConstraint iConstraint : constraints) {
			constraintsLocal.add(iConstraint);
		}

		// Sort the constraint by the length of their children
		Collections.sort(constraintsLocal, new Comparator<IConstraint>() {
			@Override
			public int compare(IConstraint o1, IConstraint o2) {
				final int o1Childs = o1.getNode().toRegularCNF().getChildren().length;
				final int o2Childs = o2.getNode().toRegularCNF().getChildren().length;
				if (o1Childs == o2Childs) {
					return 0;
				} else if (o1Childs > o2Childs) {
					return 1;
				} else {
					return -1;
				}
			}
		});

		for (int i = 0; i < constraintsLocal.size(); i++) {
			final Node cnf = constraintsLocal.get(i).getNode().toRegularCNF();
			cnfNodes.add(cnf);
			try {
				solverPush(cnf.getChildren());
			} catch (final ContradictionException e) {}
		}
		monitor.checkCancel();

		for (int j = constraintsLocal.size() - 1; j >= 0; j--) {
			final IConstraint constraint = constraintsLocal.get(j);
			boolean redundant = false;

			// Pop all constraints, which are not redundant, until we reach the constraint that should be checked for redundancy (also remove that one)
			for (int i = constraintsLocal.size() - 1; i >= 0; i--) {
				if (i >= j) {
					final IConstraint constraintStack = constraintsLocal.get(i);
					// Pop all non redundant constraints till we reach our constraint
					if (map.get(constraintStack) != ConstraintAttribute.REDUNDANT) {
						solverPop(cnfNodes.get(i).getChildren().length);
					}
				} else {
					break;
				}

			}

			// Push all constraints which where popped before except the redundant ones
			for (int i = j + 1; i < constraintsLocal.size(); i++) {
				if (i > j) {
					final IConstraint constraintStack = constraintsLocal.get(i);
					if (map.get(constraintStack) != ConstraintAttribute.REDUNDANT) {
						try {
							solverPush(cnfNodes.get(i).getChildren());
						} catch (final ContradictionException e) {}
					}
				}
			}

			final Node constraintNode = new Not(cnfNodes.get(j)).toRegularCNF();
			final Node[] clauses = constraintNode.getChildren();
			for (int i = 0; i < clauses.length; i++) {
				try {
					solverPush(clauses[i]);
				} catch (final ContradictionException e) {
					// Unsatisfiable => redundant
					redundant = true;
					solverPop(i);
				}
			}
			if (!redundant) {
				switch (solverSatisfiable()) {
				case TRUE:
				case TIMEOUT:
					solverPop(clauses.length);
					break;
				case FALSE:
					redundant = true;
					solverPop(clauses.length);
					break;
				default:
					break;
				}
			}

			if (redundant) {
				map.put(constraint, ConstraintAttribute.REDUNDANT);
			} else {
				// Pop all constraints, which are not redundant, until we reach the constraint that should be checked for redundancy (also remove that one)
				for (int i = constraintsLocal.size() - 1; i >= 0; i--) {
					if (i > j) {
						final IConstraint constraintStack = constraintsLocal.get(i);
						// Pop all non redundant constraints till we reach our constraint
						if (map.get(constraintStack) != ConstraintAttribute.REDUNDANT) {
							solverPop(cnfNodes.get(i).getChildren().length);
						}
					} else {
						break;
					}

				}

				try {
					solverPush(cnfNodes.get(j).getChildren());
				} catch (final ContradictionException e1) {}

				// Push all constraints which where popped before except the redundant ones
				for (int i = j + 1; i < constraintsLocal.size(); i++) {
					if (i > j) {
						final IConstraint constraintStack = constraintsLocal.get(i);
						if (map.get(constraintStack) != ConstraintAttribute.REDUNDANT) {
							try {
								solverPush(cnfNodes.get(i).getChildren());
							} catch (final ContradictionException e) {}
						}
					} else {
						break;
					}
				}
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
}
