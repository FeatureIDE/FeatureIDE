/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.editing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.ListIterator;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Implementation of {@link INodeCreator} using {@link Node}.</br>
 * Does not create a CNF.
 * 
 * @author Sebastian Krieter
 * 
 * @see CNFNodeCreator
 */
public class NewNodeCreator implements INodeCreator<And> {

	public And createNodes(FeatureModel featureModel) {
		final Node[] andChildren1 = createStructuralNodes(featureModel).getChildren();
		final Node[] andChildren2 = createConstraintNodes(featureModel).getChildren();

		final int length = andChildren1.length + andChildren2.length;
		final Node[] nodeArray = new Node[length + 2];
		
		System.arraycopy(andChildren1, 0, nodeArray, 0, andChildren1.length);
		System.arraycopy(andChildren2, 0, nodeArray, andChildren1.length, andChildren2.length);
		
		nodeArray[length] = new Literal(NodeCreator.varTrue);
		nodeArray[length + 1] = new Literal(NodeCreator.varFalse, false);

		return new And(nodeArray);
	}

	public And createStructuralNodes(FeatureModel featureModel) {
		final Feature root = featureModel.getRoot();
		if (root != null) {
			final List<Or> clauses = new ArrayList<>(featureModel.getNumberOfFeatures());

			clauses.add(new Or(getVariable(root, true)));

			final Collection<Feature> features = featureModel.getFeatures();
			for (Feature feature : features) {
				for (Feature child : feature.getChildren()) {
					clauses.add(new Or(getVariable(feature, true), getVariable(child, false)));
				}

				if (feature.isAnd()) {
					for (Feature child : feature.getChildren()) {
						if (child.isMandatory()) {
							clauses.add(new Or(getVariable(child, true), getVariable(feature, false)));
						}
					}
				} else if (feature.isOr()) {
					final Literal[] orLiterals = new Literal[feature.getChildrenCount() + 1];
					int i = 0;
					for (Feature child : feature.getChildren()) {
						orLiterals[i++] = getVariable(child, true);
					}
					orLiterals[i] = getVariable(feature, false);
					clauses.add(new Or(orLiterals));
				} else if (feature.isAlternative()) {
					final Literal[] alternativeLiterals = new Literal[feature.getChildrenCount() + 1];
					int i = 0;
					for (Feature child : feature.getChildren()) {
						alternativeLiterals[i++] = getVariable(child, true);
					}
					alternativeLiterals[i] = getVariable(feature, false);
					clauses.add(new Or(alternativeLiterals));

					for (ListIterator<Feature> it1 = feature.getChildren().listIterator(); it1.hasNext();) {
						final Feature feature1 = (Feature) it1.next();
						for (ListIterator<Feature> it2 = feature.getChildren().listIterator(it1.nextIndex()); it2.hasNext();) {
							clauses.add(new Or(getVariable(feature1, false), getVariable((Feature) it2.next(), false)));
						}
						
					}
				}
			}

			return new And(clauses.toArray(new Node[0]));
		}
		return new And(new Node[0]);
	}

	public And createConstraintNodes(FeatureModel featureModel) {
		final List<Node> clauses = new ArrayList<>(featureModel.getConstraints().size());

		for (Constraint constraint : featureModel.getConstraints()) {
			clauses.add(constraint.getNode().clone());
		}
		return new And(clauses.toArray(new Node[0]));
	}

	protected static Literal getVariable(Feature feature, boolean positive) {
		return new Literal(feature.getFeatureModel().getRenamingsManager().getOldName(feature.getName()), positive);
	}

}
