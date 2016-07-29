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
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * The class deadFeatures generates explanations for dead features. It uses a logic truth maintenance system (LTMS)
 * and boolean constraint propagation (BCP) which functions as an inference engine of the LTMS.
 * 
 * @author "Ananieva Sofia"
 */
public class DeadFeature {

	/**
	 * The model after a change (with a constraint that makes a feature dead).
	 */
	private static IFeatureModel model;

	/**
	 * Explains dead features or void feature models (root is equivalent to dead feature) using boolean constraint propagation. 
	 * Sets initial truth value assumptions of dead features to true and propagates them until a violation in a clause occurs.
	 * 
	 * @param featuremodel The model with the new constraint which leads to a dead feature
	 * @param deadFeature The dead features
	 * @param isVoidFM True, if explanation is generated for a void feature model. Else, false. 
	 * @return explList An explanation why the feature is dead
	 */
	public List<String> explain(IFeatureModel featuremodel, IFeature deadFeature, boolean isVoidFM) {
		List<String> explList = new ArrayList<>();
		String property = "";
		
		// add information about feature structure to explanation
		if (deadFeature.getStructure().isConcrete()) {
			property = "Concrete ";
		} else if (deadFeature.getStructure().isAbstract()) {
			property = "Abtract ";
		}
		
		setFeatureModel(featuremodel);
		Node node = NodeCreator.createNodes(model, true).toCNF();
		Node[] clauses = node.getChildren();

		// differentiate between dead feature or void feature model
		Literal deadF = new Literal(deadFeature.getName());
		if (isVoidFM) {
			explList.add("\n Feature Model is void, because: ");
		} else {
		explList.add("\n " + property + "Feature " + deadF + " is dead, because: ");
		}
		LTMS ltms = new LTMS(model);

		// generate explanation which stops after first violation with "used" clauses in stack
		List<String> tmpExplList = ltms.explainDeadFeature(clauses, deadF);

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
	 * Sets the model with the new constraint which lead to a dead feature.
	 * 
	 * @param model The model with the new constraint
	 */
	public static void setFeatureModel(IFeatureModel newModel) {
		model = newModel;
	}
}