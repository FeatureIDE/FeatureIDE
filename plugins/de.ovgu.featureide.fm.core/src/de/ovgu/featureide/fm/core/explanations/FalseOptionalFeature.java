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

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * The class FalseOptional generates explanations for false optional features. It uses a logic truth maintenance system (LTMS)
 * and boolean constraint propagation (BCP) which functions as an inference engine of the LTMS.
 * 
 * @author "Ananieva Sofia"
 */
public class FalseOptionalFeature {

	/**
	 * The model after a change (with a constraint that makes a feature false optional).
	 */
	private static IFeatureModel model;

	/**
	 * Explains false optional features using boolean constraint propagation. Sets initial truth value assumptions of false optional
	 * features to false and propagate them until a violation in any clause occurs.
	 * 
	 * @param featuremodel The model with the new constraint which leads to a false optional feature
	 * @param foFeature The false optional feature
	 * @return explList An explanation why the feature is false optional
	 */
	public List<String> explain(IFeatureModel featuremodel, IFeature foFeature) {
		List<String> explList = new ArrayList<>();
		String property = "";
		if (foFeature.getStructure().isConcrete()) {
			property = "Concrete ";
		} else if (foFeature.getStructure().isAbstract()) {
			property = "Abtract ";
		}
		setFeatureModel(featuremodel);
		Node node = NodeCreator.createNodes(model, true).toCNF();
		Node withoutTrueClauses = eliminateTrueClauses(node); // True clauses of the form True & -False & (A|B|C|True) lead to wrong BCP results
		Node[] clauses = withoutTrueClauses.getChildren();

		IFeature parentFalseOpt = FeatureUtils.getParent(foFeature);
		Literal falseOptional = new Literal(foFeature.getName());
		Literal parent = new Literal(parentFalseOpt.getName());
		explList.add("\n " + property + "Feature " + falseOptional + " is false-optional, because: ");
		LTMS ltms = new LTMS(model);

		List<String> tmpExplList = ltms.explainFalseOpsFeature(clauses, falseOptional, parent);
		if (tmpExplList.isEmpty()) {
			explList.add("No explanation possible");
		} else {
			for (String tmp : tmpExplList) {
				explList.add(" "+ tmp);
			}
		}
		return explList;
	}

	/**
	 * Removes clauses which are added in Node Creator while eliminateAbstractVariables().
	 * Such clauses are of the form True & -False & (A|B|C|True) and can be removed because
	 * they are true and don't change the semantic of a formula.
	 * 
	 * @param node The node to remove true clauses from
	 * @return updatedNodes A node without true clauses
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
	 * @param model The model with the new constraint
	 */
	public static void setFeatureModel(IFeatureModel fm) {
		model = fm;
	}
}