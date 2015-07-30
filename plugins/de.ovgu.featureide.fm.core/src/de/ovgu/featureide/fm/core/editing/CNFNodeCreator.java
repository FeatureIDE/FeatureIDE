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
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Implementation of {@link INodeCreator} using {@link Node}.</br>
 * Creates a CNF.
 * 
 * @author Sebastian Krieter
 */
public class CNFNodeCreator extends NewNodeCreator {

	public And createConstraintNodes(FeatureModel featureModel) {
		final List<Or> clauses = new ArrayList<>(featureModel.getConstraints().size());

		for (Constraint constraint : featureModel.getConstraints()) {
			final Node cnfNode = constraint.getNode().clone().toCNF();
			if (cnfNode instanceof And) {
				for (Node andChild : cnfNode.getChildren()) {
					if (andChild instanceof Or) {
						final Node[] orChildren = andChild.getChildren();
						clauses.add(new Or(Arrays.copyOf(orChildren, orChildren.length, Literal[].class)));
					} else {
						clauses.add(new Or((Literal) andChild));
					}
				}
			} else if (cnfNode instanceof Or) {
				final Node[] orChildren = cnfNode.getChildren();
				clauses.add(new Or(Arrays.copyOf(orChildren, orChildren.length, Literal[].class)));
			} else {
				clauses.add(new Or((Literal) cnfNode));
			}
		}
		return new And(clauses.toArray(new Node[0]));
	}

}
