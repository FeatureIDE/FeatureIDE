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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;

/**
 * Implementation of {@link INodeCreator} using {@link Clause}.</br>
 * Creates a CNF.
 * 
 * @author Sebastian Krieter
 * 
 */
public class CNFClauseCreator implements INodeCreator<List<Clause>> {

	public List<Clause> createNodes(FeatureModel featureModel) {
		final List<Clause> clauses = new ArrayList<>();
		clauses.addAll(createStructuralNodes(featureModel));
		clauses.addAll(createConstraintNodes(featureModel));
		return clauses;
	}

	public List<Clause> createStructuralNodes(FeatureModel featureModel) {
//		final Feature root = featureModel.getRoot();
//		if (root != null) {
//			final List<Clause> clauses = new ArrayList<>(featureModel.getNumberOfFeatures());
//
//			clauses.add(new Clause(getVariable(root, true)));
//
//			final Collection<Feature> features = featureModel.getFeatures();
//			for (Feature feature : features) {
//				for (Feature child : feature.getChildren()) {
//					clauses.add(new Clause(getVariable(feature, true), getVariable(child, false)));
//				}
//
//				if (feature.isAnd()) {
//					for (Feature child : feature.getChildren()) {
//						if (child.isMandatory()) {
//							clauses.add(new Clause(getVariable(child, true), getVariable(feature, false)));
//						}
//					}
//				} else if (feature.isOr()) {
//					final Literal[] orLiterals = new Literal[feature.getChildrenCount() + 1];
//					int i = 0;
//					for (Feature child : feature.getChildren()) {
//						orLiterals[i++] = getVariable(child, true);
//					}
//					orLiterals[i] = getVariable(feature, false);
//					clauses.add(new Clause(orLiterals));
//				} else if (feature.isAlternative()) {
//					final Literal[] alternativeLiterals = new Literal[feature.getChildrenCount() + 1];
//					int i = 0;
//					for (Feature child : feature.getChildren()) {
//						alternativeLiterals[i++] = getVariable(child, true);
//					}
//					alternativeLiterals[i] = getVariable(feature, false);
//					clauses.add(new Clause(alternativeLiterals));
//
//					for (Feature child1 : feature.getChildren()) {
//						for (Feature child2 : feature.getChildren()) {
//							clauses.add(new Clause(getVariable(child1, false), getVariable(child2, false)));
//						}
//					}
//				}
//			}
//
//			return clauses;
//		}
		return Collections.emptyList();
	}

	public List<Clause> createConstraintNodes(FeatureModel featureModel) {
		final List<Clause> clauses = new ArrayList<>(featureModel.getConstraints().size());

//		for (Constraint constraint : featureModel.getConstraints()) {
//			final Node cnfNode = constraint.getNode().clone().toCNF();
//			if (cnfNode instanceof And) {
//				for (Node andChild : cnfNode.getChildren()) {
//					if (andChild instanceof Or) {
//						final Node[] orChildren = andChild.getChildren();
//						clauses.add(new Clause(Arrays.copyOf(orChildren, orChildren.length, Literal[].class)));
//					} else {
//						clauses.add(new Clause((Literal) andChild));
//					}
//				}
//			} else if (cnfNode instanceof Or) {
//				final Node[] orChildren = cnfNode.getChildren();
//				clauses.add(new Clause(Arrays.copyOf(orChildren, orChildren.length, Literal[].class)));
//			} else {
//				clauses.add(new Clause((Literal) cnfNode));
//			}
//		}
		return clauses;
	}

	private static Literal getVariable(Feature feature, boolean positive) {
		return new Literal(feature.getFeatureModel().getRenamingsManager().getOldName(feature.getName()), positive);
	}

}
