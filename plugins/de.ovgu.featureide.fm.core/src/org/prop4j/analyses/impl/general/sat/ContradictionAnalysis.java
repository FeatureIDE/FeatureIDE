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
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.SatResult;
import org.prop4j.solver.impl.SolverManager;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * This analysis finds contradiction in the given constraints. The analysis can be used as feature model dependent (FM+Constraints) or indipendent (Constraints
 * only) contradiction analysis. This is decided wether the given {@link ISatSolver} or {@link ISatProblem} contain the structure of the feature model or not.
 * The creation of the feture models structure without constraints can be achieved by with the help of the {@link AdvancedNodeCreator} as shown below:
 *
 * <br><br><code> nodeCreator.setModelType(ModelType.OnlyStructure); <br> final ISatProblem structureModelProblem = new SatProblem(nodeCreator.createNodes());
 * </code>
 *
 * <br><br> and for the complete feature model with constraints:
 *
 * <br><br><code> nodeCreator.setModelType(ModelType.All); <br> final ISatProblem structureModelProblem = new SatProblem(nodeCreator.createNodes()); </code>
 *
 * <br><br> The return value of the analysis is a subset from the passed constraints.
 *
 * @see AdvancedNodeCreator#setModelType(de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType)
 * @see AdvancedNodeCreator#createNodes()
 *
 * @author Joshua Sprey
 */
public class ContradictionAnalysis extends AbstractSatSolverAnalysis<List<IConstraint>> {

	/** Contains the list of all constraints that should be check on contradicitons. */
	List<IConstraint> constraints;

	public ContradictionAnalysis(ISatSolver solver, List<IConstraint> constraints) {
		super(solver);
		this.constraints = constraints;
	}

	public ContradictionAnalysis(ISatProblem problemInstance, List<IConstraint> constraints) {
		super(problemInstance);
		this.constraints = constraints;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.analyses.impl.general.sat.AbstractSatSolverAnalysis#initSolver(org.prop4j.solver.ISatProblem)
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
		final List<IConstraint> result = new ArrayList<IConstraint>();
		// If given constraint are empty return empty list
		if ((constraints == null) || constraints.isEmpty()) {
			return result;
		}

		// Save, or if needed create, the node representation for the given constraints.
		final Node[] constraintsNodeCNF = new Node[constraints.size()];
		for (int i = 0; i < constraints.size(); i++) {
			if (constraints.get(i).getNode().isConjunctiveNormalForm()) {
				constraintsNodeCNF[i] = constraints.get(i).getNode();
			} else {
				constraintsNodeCNF[i] = constraints.get(i).getNode().toRegularCNF();
			}
		}

		// Test every constraint if contradiciton

		for (int i = 0; i < constraints.size(); i++) {
			try {
				solver.push(constraintsNodeCNF[i]);
			} catch (final ContradictionException e) {
				// contradiction => add to result
				result.add(constraints.get(i));
				// No pop needed because the contradiciton prevented the push of the constraint
				continue;
			}

			// Not every solver can detect contradictions when adding clauses. Therefore we need to perform a satisfiability check to determine whether the
			// constraint is a contradiciton or not
			final SatResult hasSolution = getSolver().isSatisfiable();
			switch (hasSolution) {
			case FALSE:
				// contradiction => add to result
				result.add(constraints.get(i));
				getSolver().pop(); // remove constraint from solver
				break;
			case TIMEOUT:
				reportTimeout();
				break;
			case TRUE:
				break;
			default:
				throw new AssertionError(hasSolution);
			}
		}
		return result;
	}

}
