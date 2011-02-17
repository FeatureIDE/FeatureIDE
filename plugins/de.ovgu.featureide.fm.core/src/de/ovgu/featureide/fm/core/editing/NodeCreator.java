/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.core.editing;

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

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;


/**
 * Takes a feature model as input and returns a propositional formula
 * representing the valid feature combinations.
 * 
 * @author Thomas Thuem
 */
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
//			createNodes(nodes, root, featureModel, true, replacingMap);
			createNodes(nodes, root, featureModel, true, EMPTY_MAP);
			//add extra constraints
			for (Node node : featureModel.getPropositionalNodes())
				nodes.add(node.clone());
		}
		Node node = new And(nodes);
		System.out.println(node);
		node = eliminateAbstractVariables2(node, featureModel);
		System.out.println(node);
		return node;
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
	
	// Using objects for true and false instead of strings ensures, that the
	// user cannot choose the same name by accident. Overriding the toString
	// method is just for convenient printing of formulas.
	private final static Object litTrue = new Object() {
		public String toString() {
			return "True";
		};
	};
	private final static Object litFalse = new Object() {
		public String toString() {
			return "False";
		};
	};
	
	public static Node eliminateAbstractVariables2(Node node, FeatureModel featureModel) {
		int concreteCount = 0;
		for (Feature feature : featureModel.getFeatures())
			if (feature.isAbstract()) {
				String name = getVariable(feature, featureModel);
				Node trueNode = replaceFeature(node.clone(), name, litTrue);
				Node falseNode = replaceFeature(node.clone(), name, litFalse);
				node = new Or(trueNode, falseNode);
				node = simplify(node);
			}
			else
				concreteCount++;
		Node[] concreteFeatures = new Node[concreteCount + 1];
		int i = 0;
		for (Feature feature : featureModel.getFeatures())
			if (feature.isConcrete())
				concreteFeatures[i++] = new Literal(getVariable(feature, featureModel));
		concreteFeatures[i] = new Literal(litTrue);
		node = new And(node, litTrue, new Not(litFalse), new Or(concreteFeatures));
		return node;
	}
	
	private static Node simplify(Node node) {
		if (node instanceof Literal) {
			Literal lit = (Literal) node;
			if (lit.var.equals(litFalse) && !lit.positive)
				return new Literal(litTrue);
			if (lit.var.equals(litTrue) && !lit.positive)
				return new Literal(litFalse);
			return lit;
		}
		Node[] children = node.getChildren();
		int removeChildren = 0;
		for (int i = 0; i < children.length; i++) {
			Node child = simplify(children[i]);
			if (child instanceof Literal) {
				Literal lit = (Literal) child;
				//we assume that litTrue and litFalse can only occur positive
				if (lit.var.equals(litTrue)) {
					if (node instanceof Not)
						return new Literal(litFalse);
					if (node instanceof And) {
						removeChildren++;
						child = null;
					}
					if (node instanceof Or)
						return lit;
					if (node instanceof Implies) {
						if (i == 0)
							return children[1];
						else
							return lit;
					}
					if (node instanceof Equals) {
						if (i == 0)
							return children[1];
						else
							return children[0];
					}
				}
				else if (lit.var.equals(litFalse)) {
					if (node instanceof Not)
						return new Literal(litTrue);
					if (node instanceof And)
						return lit;
					if (node instanceof Or) {
						removeChildren++;
						child = null;
					}
					if (node instanceof Implies) {
						if (i == 0)
							return new Literal(litTrue);
						else
							return simplify(new Not(children[0]));
					}
					if (node instanceof Equals) {
						if (i == 0)
							return simplify(new Not(children[1]));
						else
							return simplify(new Not(children[0]));
					}
				}
			}
			children[i] = child;
		}
		if (removeChildren == 0)
			return node;
		if (children.length - removeChildren == 0) {
			if (node instanceof And)
				return new Literal(litTrue);
			if (node instanceof Or)
				return new Literal(litFalse);
		}
		Node[] newChildren = new Node[children.length - removeChildren];
		int i = 0;
		for (Node child : children)
			if (child != null)
				newChildren[i++] = child;
		node.setChildren(newChildren);
		return node;
	}

	private static Node replaceFeature(Node node, Object abstractFeature,
			Object replacement) {
		if (node instanceof Literal) {
			Literal lit = (Literal) node;
			if (lit.var.equals(abstractFeature))
				return new Literal(replacement, lit.positive);
			else
				return node;
		}
		Node[] children = node.getChildren();
		for (int i = 0; i < children.length; i++)
			children[i] = replaceFeature(children[i], abstractFeature, replacement);
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
//				if (rootFeature.isAbstract())
//					nodes.add(new Equals(definition, new Literal(s)));
//				else 
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
