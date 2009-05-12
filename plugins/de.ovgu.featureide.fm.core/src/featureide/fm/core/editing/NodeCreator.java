/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.core.editing;

import java.util.HashMap;
import java.util.LinkedList;

import org.prop4j.And;
import org.prop4j.AtMost;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;

public class NodeCreator {
	
	private static final HashMap<Object, Node> EMPTY_MAP = new HashMap<Object, Node>();

	public static Node createNodes(FeatureModel featureModel) {
		return createNodes(featureModel, EMPTY_MAP);
	}
	
	public static Node createNodes(FeatureModel featureModel, HashMap<Object, Node> replacingMap) {
		Feature root = featureModel.getRoot();
		LinkedList<Node> nodes = new LinkedList<Node>();
		if (root != null) {
			nodes.add(new Literal(getVariable(root, featureModel)));
			//convert grammar rules into propositional formulas
			createNodes(nodes, root, featureModel, true, replacingMap);
			//add extra constraints
			for (Node node : featureModel.getPropositionalNodes())
				nodes.add(node.clone());
		}
		return eliminateAbstractVariables(new And(nodes), replacingMap);
	}
	
	public static Node eliminateAbstractVariables(Node node, HashMap<Object, Node> map) {
		if (node instanceof Literal) {
			Literal literal = (Literal) node;
			if (map.containsKey(literal.var)) {
				Node replacing = map.get(literal.var);
				node = literal.positive ? replacing : new Not(replacing);
			}
		}
		else {
			Node[] children = node.getChildren();
			for (int i = 0; i < children.length; i++)
				children[i] = eliminateAbstractVariables(children[i], map);
		}
		return node;
	}
	
	private static void createNodes(LinkedList<Node> nodes, Feature rootFeature, FeatureModel featureModel, boolean recursive, HashMap<Object, Node> replacings) {
		if (rootFeature == null || !rootFeature.hasChildren())
			return;
		
		String s = getVariable(rootFeature, featureModel);
		
		Node[] children = new Node[rootFeature.getChildrenCount()];
		for (int i = 0; i < children.length; i++) {
			String var = getVariable(rootFeature.getChildren().get(i), featureModel);
			children[i] = new Literal(var);
		}
		Node definition = children.length == 1 ? children[0] : new Or(children);

		if (rootFeature.isAnd()) {// && (!replacings.containsKey(featureModel.getOldName(rootFeature.getName())) || !rootFeature.isPossibleEmpty())) {
			LinkedList<Node> manChildren = new LinkedList<Node>();
			for (Feature feature : rootFeature.getChildren())
				if (feature.isMandatory()) {
					String var = getVariable(feature, featureModel);
					manChildren.add(new Literal(var));
				}

			//add constraints for all mandatory children S => (A & B)
			if (manChildren.size() == 1)
				nodes.add(new Implies(new Literal(s), manChildren.getFirst()));
			else if (manChildren.size() > 1)
				nodes.add(new Implies(new Literal(s), new And(manChildren)));

			//add contraint (A | B | C) => S
			if (!replacings.containsKey(featureModel.getOldName(rootFeature.getName()))) {
				if (rootFeature.isAbstract())
					nodes.add(new Equals(definition, new Literal(s)));
				else 
					nodes.add(new Implies(definition, new Literal(s)));
			}
		}
		else {
			//add constraint S <=> (A | B | C)
			if (!replacings.containsKey(featureModel.getOldName(rootFeature.getName()))) {
				nodes.add(new Equals(new Literal(s), definition));
			}
			
			if (rootFeature.isAlternative()) {
				//add constraint atmost1(A, B, C)
				if (children.length > 1)
					nodes.add(new AtMost(1, Node.clone(children)));
			}
		}
		
		if (recursive)
			for (Feature feature : rootFeature.getChildren())
				createNodes(nodes, feature, featureModel, true, replacings);
	}
	
	public static String getVariable(Feature feature, FeatureModel featureModel) {
		return featureModel.getOldName(feature.getName());
	}
	

}
