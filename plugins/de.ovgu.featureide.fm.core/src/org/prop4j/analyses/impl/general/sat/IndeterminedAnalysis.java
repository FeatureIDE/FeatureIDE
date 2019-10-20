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
import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.SatResult;
import org.prop4j.solver.impl.SolverManager;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * TODO SOLVER description
 *
 * @author Joshua
 */
public class IndeterminedAnalysis extends AbstractSatSolverAnalysis<List<IFeature>> {

	int[] hiddenFeatures;

	public IndeterminedAnalysis(ISatProblem problem, int[] hiddenFeatures) {
		super(problem);
		this.hiddenFeatures = hiddenFeatures;
	}

	public IndeterminedAnalysis(ISatSolver solver, int[] hiddenFeatures) {
		super(solver);
		this.hiddenFeatures = hiddenFeatures;
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
	protected List<IFeature> analyze(IMonitor<List<IFeature>> monitor) throws Exception {
		monitor.setRemainingWork(2 * hiddenFeatures.length);

		final LinkedList<Integer> potentialResultList = new LinkedList<Integer>();
		final List<Node> relevantClauses = new ArrayList<>();

		for (final int literal : hiddenFeatures) {
			final List<Node> clauses = getSolver().getClauses();
			for (final Node clause : clauses) {
				final Literal lit = getSolver().getProblem().getVariableAsNode(literal);
				if (nodeContainLiteral(clause, lit)) {
					final Node newClause = eliminateLiteral(clause, getSolver().getProblem().getVariableAsNode(literal));
					if (newClause != null) {
						relevantClauses.add(newClause);
					}
				}
			}
			try {
				getSolver().push((Node[]) relevantClauses.toArray(new Node[relevantClauses.size()]));
			} catch (final ContradictionException e) {
				relevantClauses.clear();
				monitor.step();
				continue;
			}

			final SatResult hasSolution = getSolver().isSatisfiable();
			switch (hasSolution) {
			case FALSE:
				break;
			case TIMEOUT:
				reportTimeout();
				break;
			case TRUE:
				potentialResultList.push(literal);
				break;
			default:
				throw new AssertionError(hasSolution);
			}
			getSolver().popAll();
			relevantClauses.clear();
			monitor.step();
		}

		return null;
	}

	private boolean nodeContainLiteral(final Node clause, final Literal lit) {
		return clause.getContainedFeatures().contains(lit.var);
	}

	private Node eliminateLiteral(Node node, Literal lit) {
		if ((node instanceof And) || (node instanceof Or)) {
			if (node.getChildren() != null) {
				final List<Node> newChildren = new ArrayList<>();
				// Eliminate for all children and skip null values
				for (final Node nodeChild : node.getChildren()) {
					final Node result = eliminateLiteral(nodeChild, lit);
					if (result != null) {
						newChildren.add(result);
					}
				}
				if (node instanceof And) {
					return new And((Node[]) newChildren.toArray(new Node[newChildren.size()]));
				} else {
					return new Or((Node[]) newChildren.toArray(new Node[newChildren.size()]));
				}
			}
		} else if (node instanceof Literal) {
			if (((Literal) node).var == lit.var) {
				return null;
			} else {
				return node;
			}
		}
		return null;
	}
}
