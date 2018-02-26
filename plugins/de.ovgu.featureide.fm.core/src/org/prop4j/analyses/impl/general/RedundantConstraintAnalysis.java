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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.analyses.AbstractSolverAnalysisFactory;
import org.prop4j.analyses.GeneralSolverAnalysis;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISolver;
import org.prop4j.solver.impl.SatProblem;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

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
		for (final IConstraint constraint : constraints) {
			final Node cnf = constraint.getNode().toRegularCNF();
			cnfNodes.add(cnf);
		}
		monitor.checkCancel();

		int i = -1;
		for (final IConstraint constraint : constraints) {
			i++;
			boolean redundant = true;

			final Node constraintNode = cnfNodes.get(i);
			final Node[] clauses = constraintNode.getChildren();
			for (int j = 0; j < clauses.length; j++) {
				if (!isImplied(clauses[j].getChildren())) {
					redundant = false;
					try {
						solver.push(constraintNode);
					} catch (final ContradictionException e) {
						FMCorePlugin.getDefault().logError(e);
					}
					break;
				}
			}

			if (redundant) {
				if (checkConstraintTautology(constraint.getNode())) {
					map.put(constraint, ConstraintAttribute.TAUTOLOGY);
				} else {
					map.put(constraint, ConstraintAttribute.REDUNDANT);
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

	public boolean isImplied(Node... or) {
		// Add the variables as assumptions
		for (int i = 0; i < or.length; i++) {
			final Literal node = (Literal) or[i];
			try {
				solver.push(new Literal(node.var, !node.positive));
			} catch (final ContradictionException e) {
				solver.pop(i);	// Removes the pushed assumptions
				return true;
			}
		}
		switch (solver.isSatisfiable()) {
		case FALSE:
			solver.pop(or.length);	// Removes the pushed assumptions
			return true;
		case TIMEOUT:
		case TRUE:
		default:
			solver.pop(or.length); // Removes the pushed assumptions
			return false;
		}
	}

	private boolean checkConstraintTautology(Node constraintNode) {
		return checkConstraintContradiction(new Not(constraintNode).toRegularCNF());
	}

	private boolean checkConstraintContradiction(Node constraintNode) {
		final ISatProblem problem = new SatProblem(constraintNode);
		final org.prop4j.analyses.impl.general.ValidAnalysis validAnalysis =
			(org.prop4j.analyses.impl.general.ValidAnalysis) factory.getAnalysis(org.prop4j.analyses.impl.general.ValidAnalysis.class, problem);

		final Object[] solution = LongRunningWrapper.runMethod(validAnalysis, new NullMonitor());

		return solution == null;
	}
}
