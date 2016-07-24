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

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.ModifiableSolver;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Finds redundant constraints of a sub model.
 * 
 * @author Sebastian Krieter
 */
public class SubModelRedundantAnalysis implements LongRunningMethod<List<IConstraint>> {

	private final List<IConstraint> constraints;

	private boolean valid;

	private IFeatureModel fm;
	private AdvancedNodeCreator nodeCreator;

	public SubModelRedundantAnalysis(IFeatureModel fm, List<IConstraint> constraints) {
		this.fm = fm;
		this.constraints = constraints;

		nodeCreator = new AdvancedNodeCreator(fm);
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(false);
		nodeCreator.setUseOldNames(false);
	}

	public boolean isValid() {
		return valid;
	}

	/**
	 * Detects redundancy of a constraint by checking if the model without the new (possibly redundant) constraint
	 * implies the model with the new constraint and the other way round. If this is the case, both models are
	 * equivalent and the constraint is redundant.
	 * If a redundant constraint has been detected, it is explained.
	 * 
	 * @param constraint The constraint to check whether it is redundant
	 */
	public List<IConstraint> execute(WorkMonitor monitor) throws Exception {
		final ArrayList<IConstraint> result = new ArrayList<>();
		checkValidity(new SatInstance(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm)));
		if (valid) {
			nodeCreator.setModelType(ModelType.All);
			final SatInstance si = new SatInstance(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
			final ModifiableSolver redundantSat = new ModifiableSolver(si);

			final List<Node> cnfNodes = new ArrayList<>();
			for (IConstraint constraint : constraints) {
				Node cnf = makeRegular(constraint.getNode());
				cnfNodes.add(cnf);
			}
			monitor.step();

			int i = -1;
			for (IConstraint constraint : constraints) {
				i++;
				boolean redundant = true;
				final Node constraintNode = cnfNodes.get(i);

				final Node[] clauses = constraintNode.getChildren();
				for (int j = 0; j < clauses.length; j++) {
					if (!redundantSat.isImplied(clauses[j].getChildren())) {
						redundant = false;
						break;
					}
				}

				if (redundant) {
					result.add(constraint);
				}
			}
		}
		return result;
	}

	private void checkValidity(final SatInstance si) {
		valid = LongRunningWrapper.runMethod(new FindSolutionAnalysis(si)) != null;
	}

	private Node makeRegular(Node node) {
		Node regularCNFNode = node.toCNF();
		if (regularCNFNode instanceof And) {
			final Node[] children = regularCNFNode.getChildren();
			for (int i = 0; i < children.length; i++) {
				final Node child = children[i];
				if (child instanceof Literal) {
					children[i] = new Or(child);
				}
			}
		} else if (regularCNFNode instanceof Or) {
			regularCNFNode = new And(regularCNFNode);
		} else if (regularCNFNode instanceof Literal) {
			regularCNFNode = new And(new Or(regularCNFNode));
		}
		return regularCNFNode;
	}

}
