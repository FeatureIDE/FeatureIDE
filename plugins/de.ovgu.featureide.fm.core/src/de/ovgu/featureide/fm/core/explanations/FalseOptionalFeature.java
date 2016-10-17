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

import java.util.LinkedList;

import org.prop4j.And;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Generates explanations for false-optional features using {@link LTMS}.
 * 
 * @author Sofia Ananieva
 * @author Timo Guenther
 */
public class FalseOptionalFeature {
	/**
	 * Returns an explanation why the given feature of the given feature model is false-optional.
	 * Sets initial truth value assumptions of the false-optional feature to false and its parent to true.
	 * Then propagates the values until a violation in a clause occurs.
	 * @param fm the model with the new constraint which leads to a false-optional feature
	 * @param defectFeature the false-optional feature
	 * @return an explanation why the given feature of the given feature model is false-optional
	 */
	public Explanation explain(IFeatureModel fm, IFeature defectFeature) {
		Node cnf = NodeCreator.createNodes(fm, true).toCNF();
		cnf = eliminateTrueClauses(cnf);
		final LTMS ltms = new LTMS(cnf);
		ltms.addPremise(defectFeature.getName(), false);
		ltms.addPremise(FeatureUtils.getParent(defectFeature).getName(), true);
		final Explanation explanation = ltms.getExplanation();
		explanation.setDefectFalseOptionalFeature(defectFeature);
		explanation.setFeatureModel(fm);
		return explanation;
	}
	
	/**
	 * Removes clauses which are added in Node Creator while eliminateAbstractVariables().
	 * Such clauses are of the form True & -False & (A|B|C|True) and can be removed because
	 * they are true and don't change the semantic of a formula.
	 * @param node the node to remove true clauses from
	 * @return a node without true clauses
	 */
	private static Node eliminateTrueClauses(Node node) {
		LinkedList<Node> updatedNodes = new LinkedList<Node>();
		for (Node child : node.getChildren())
			if (!child.toString().contains("True") && !child.toString().contains("False"))
				updatedNodes.add(child);
		return updatedNodes.isEmpty() ? null : new And(updatedNodes);
	}
}