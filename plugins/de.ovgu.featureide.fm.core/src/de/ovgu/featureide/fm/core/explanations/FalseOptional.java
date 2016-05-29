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
package de.ovgu.featureide.fm.core.explanations;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * The class FalseOptional generates explanations for false optional features. It uses a logic truth maintenance system (LTMS)
 * and its boolean constraint propagation (BCP).
 * 
 * @author "Ananieva Sofia"
 */
public class FalseOptional {

	/**
	 * The model after a change (with a constraint that makes a feature false optional).
	 */
	private IFeatureModel model;

	/**
	 * Explains false optional features using boolean constraint propagation. Sets initial truth value assumptions of false optional
	 * features to false and propagate them until a violation in any clause occurs.
	 * 
	 * @param newModel the model with the new constraint which leads to a false optional feature
	 * @param falsOptionals a list of false optional features
	 * @return String an explanation why the feature(s) is false optional
	 */
	public String explain(IFeatureModel newModel, Collection<IFeature> falseOptionals) {
		String reason = "";
		setNewModel(newModel);
		Node node = NodeCreator.createNodes(model, true).toCNF();
		Node withoutTrueClauses = eliminateTrueClauses(node);
		Node[] clauses = withoutTrueClauses.getChildren();

		for (IFeature falsopt : falseOptionals) {
			Literal falseOptional = new Literal(falsopt.getName());
			LTMS ltms = new LTMS(model);
			String tmpReason = "Feature " + falseOptional + " is false-optional, because: \n";

			List<String> explList = ltms.explainFalseOpsFeature(clauses, falseOptional);
			if (explList.isEmpty()){
				tmpReason += "No explanation possible, some parent might be dead";
			}
			else{	
				for (String tmp : explList) {
					tmpReason += tmp + ",\n";
				}
				int lastChar = tmpReason.lastIndexOf(",");
				tmpReason = tmpReason.substring(0, lastChar);
			}
			reason += tmpReason + "\n\n";
		}
		return reason.trim();
	}

	/**
	 * Removes clauses which are added in Node Creator while eliminateAbstractVariables().
	 * Such clauses are of the form True & -False & (A|B|C|True) and can be removed because
	 * they are true and don't change the semantic of a formula.
	 * 
	 * @param node the formula node to remove true clauses from
	 * @return formula node without true clauses
	 */
	private Node eliminateTrueClauses(Node node) {
		LinkedList<Node> updatedNodes = new LinkedList<Node>();
		for (Node child : node.getChildren())
			if (!child.toString().contains("True") && !child.toString().contains("False"))
				updatedNodes.add(child);
		return updatedNodes.isEmpty() ? null : new And(updatedNodes);
	}

	/**
	 * Sets the model with the new constraint which lead to a dead feature.
	 * 
	 * @param model the model with the new constraint
	 */
	private void setNewModel(IFeatureModel newModel) {
		model = newModel;
	}

	/**
	 * Gets the model with the new constraint. Used for tooltips to get the correct constraint index.
	 * 
	 * @return the model with the new constraint
	 */
	public IFeatureModel getNewModel() {
		return model;
	}
}