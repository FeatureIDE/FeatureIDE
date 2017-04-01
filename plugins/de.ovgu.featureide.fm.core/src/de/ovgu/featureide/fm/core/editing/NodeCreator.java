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
package de.ovgu.featureide.fm.core.editing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.prop4j.And;
import org.prop4j.AtMost;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Takes a feature model as input and returns a propositional formula
 * representing the valid feature combinations.
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class NodeCreator {
	public static Node createNodes(IFeatureModel featureModel) {
		return createNodes(featureModel, true);
	}

	public static Node createNodes(IFeatureModel featureModel, boolean ignoreAbstractFeatures) {
		return createNodes(featureModel, ignoreAbstractFeatures ? Collections.<Object, Node>emptyMap() : calculateReplacingMap(featureModel));
	}

	public static Node createNodes(IFeatureModel featureModel, Collection<String> removeFeatures) {
		return createNodes(featureModel, calculateReplacingMap(featureModel, removeFeatures), removeFeatures);
	}

	/**
	 * Adds an encoded constraint index to literals of this constraint. If a cross-tree-constraint
	 * is needed for an explanation, the constrained index is decoded. 
	 * 
	 * @param node the constraint to set its index
	 * @param constraintIndex the index of a cross-tree constraint
	 */
	static void addConstraintIndexRec(Node node, int constraintIndex) {
		if (node == null)
			return;

		if (node instanceof Literal) {
			((Literal) node).setOriginConstraint(constraintIndex);

			return;
		}

		if (node.getChildren() != null) {
			for (Node child : node.getChildren()) {
				addConstraintIndexRec(child, constraintIndex);
			}
		}
	}
	
	public static Node createNodes(IFeatureModel featureModel, Map<Object, Node> replacingMap) {
		IFeature root = FeatureUtils.getRoot(featureModel);
		List<Node> nodes = new LinkedList<>();
		if (root != null) {
			nodes.add(new Literal(getVariable(root.getName(), featureModel), Literal.FeatureAttribute.ROOT));
			// convert grammar rules into propositional formulas
			createNodes(nodes, root, featureModel, true, replacingMap);
			// add extra constraints
			for (IConstraint constraint : new ArrayList<>(featureModel.getConstraints())) {
				Node node = constraint.getNode();
				addConstraintIndexRec(node, FeatureUtils.getConstraintIndex(featureModel, constraint));
				nodes.add(node.clone());
			}
		}
		And and = new And(nodes);
		and = (And) replaceAbstractVariables(and, replacingMap, false);
		and = eliminateAbstractVariables(and, replacingMap, featureModel);
		return replaceNames(and, featureModel);
	}

	public static Node createNodes(IFeatureModel featureModel, Map<Object, Node> replacingMap, Collection<String> removeFeatures) {
		IFeature root = FeatureUtils.getRoot(featureModel);
		List<Node> nodes = new LinkedList<>();
		if (root != null) {
			nodes.add(new Literal(getVariable(root.getName(), featureModel)));
			// convert grammar rules into propositional formulas
			createNodes(nodes, root, featureModel, true, replacingMap);
			// add extra constraints
			for (IConstraint constraint : new ArrayList<>(featureModel.getConstraints()))
				nodes.add(constraint.getNode().clone());
		}
		And and = new And(nodes);
		and = (And) replaceAbstractVariables(and, replacingMap, false);
		and = eliminateAbstractVariables(and, replacingMap, featureModel, removeFeatures);
		return replaceNames(and, featureModel);
	}

	/**
	 * @param and
	 * @param featureModel
	 * @return
	 */
	private static Node replaceNames(Node node, IFeatureModel featureModel) {
		if (node == null) {
			return null;
		}
		if (node instanceof Literal) {
			Literal literal = (Literal) node;
			if (literal.var instanceof String) {
				literal.var = featureModel.getRenamingsManager().getOldName((String) literal.var);
			}
		} else {
			Node[] children = node.getChildren();
			for (int i = 0; i < children.length; i++) {
				children[i] = replaceNames(children[i], featureModel);
				if (children[i] == null)
					return null;
			}
		}

		return node;
	}

	public static Node replaceAbstractVariables(Node node, Map<Object, Node> map, boolean replaceNull) {
		if (node == null)
			return null;
		if (node instanceof Literal) {
			Literal literal = (Literal) node;
			if (map.containsKey(literal.var)) {
				Node replacing = map.get(literal.var);
				if (replacing == null)
					return replaceNull ? null : node;
				replacing = replacing.clone();
				node = literal.positive ? replacing : new Not(replacing);
			}
		} else {
			Node[] children = node.getChildren();
			for (int i = 0; i < children.length; i++) {
				children[i] = replaceAbstractVariables(children[i], map, replaceNull);
				if (replaceNull && children[i] == null)
					return null;
			}
		}
		return node;
	}

	// Using objects for true and false instead of strings ensures, that the
	// user cannot choose the same name by accident. Overriding the toString
	// method is just for convenient printing of formulas.
	public final static Object varTrue = new Object() {
		public String toString() {
			return "True";
		};
	};
	public final static Object varFalse = new Object() {
		public String toString() {
			return "False";
		};
	};

	public static And eliminateAbstractVariables(And and, Map<Object, Node> map, IFeatureModel featureModel) {
		for (Entry<Object, Node> entry : map.entrySet())
			if (entry.getValue() == null) {
				String name = entry.getKey().toString();
				List<Node> nochange = new LinkedList<>();
				List<Node> change = new LinkedList<>();
				calculateNodesToReplace(and.getChildren(), name, nochange, change);
				if (!change.isEmpty()) {
					Node toChange = new And(change);
					Node trueNode = replaceFeature(toChange.clone(), name, varTrue);
					Node falseNode = replaceFeature(toChange.clone(), name, varFalse);
					Node newPart = simplify(new Or(trueNode, falseNode));
					newPart = simplify(newPart.toCNF());
					if (!(newPart instanceof And))
						newPart = new And(newPart);
					Node[] children = new Node[nochange.size() + newPart.getChildren().length];
					int i = 0;
					for (Node child : nochange)
						children[i++] = child;
					for (Node child : newPart.getChildren())
						children[i++] = child;
					and = new And(children);
				}
			}
		Node[] concreteFeatures = new Node[featureModel.getAnalyser().countConcreteFeatures() + 1];
		int i = 0;
		for (IFeature feature : featureModel.getFeatures())
			if (feature.getStructure().isConcrete())
				concreteFeatures[i++] = new Literal(getVariable(feature.getName(), featureModel));
		concreteFeatures[i] = new Literal(varTrue);
		return new And(and, varTrue, new Not(varFalse), new Or(concreteFeatures));
	}

	public static And eliminateAbstractVariables(And and, Map<Object, Node> map, IFeatureModel featureModel, Collection<String> removeFeatures) {
		for (Entry<Object, Node> entry : map.entrySet())
			if (entry.getValue() == null) {
				String name = entry.getKey().toString();
				List<Node> nochange = new LinkedList<>();
				List<Node> change = new LinkedList<>();
				calculateNodesToReplace(and.getChildren(), name, nochange, change);
				if (!change.isEmpty()) {
					Node toChange = new And(change);
					Node trueNode = replaceFeature(toChange.clone(), name, varTrue);
					Node falseNode = replaceFeature(toChange.clone(), name, varFalse);
					Node newPart = simplify(new Or(trueNode, falseNode));
					newPart = simplify(newPart.toCNF());
					if (!(newPart instanceof And))
						newPart = new And(newPart);
					Node[] children = new Node[nochange.size() + newPart.getChildren().length];
					int i = 0;
					for (Node child : nochange)
						children[i++] = child;
					for (Node child : newPart.getChildren())
						children[i++] = child;
					and = new And(children);
				}
			}

		final Collection<IFeature> features = Functional.toList(featureModel.getFeatures());
		List<Node> featureList = new ArrayList<>(features.size() - removeFeatures.size());
		for (IFeature feature : features) {
			if (!removeFeatures.contains(feature.getName())) {
				featureList.add(new Literal(getVariable(feature.getName(), featureModel)));
			}
		}
		Node[] concreteFeatures = new Node[featureList.size() + 1];
		featureList.toArray(concreteFeatures);

		concreteFeatures[concreteFeatures.length - 1] = new Literal(varTrue);
		return new And(and, varTrue, new Not(varFalse), new Or(concreteFeatures));
	}

	private static void calculateNodesToReplace(Node[] children, String abstractFeature, List<Node> nochange, List<Node> change) {
		for (Node node : children)
			if (nodeContains(node, abstractFeature))
				change.add(node);
			else
				nochange.add(node);
	}

	private static boolean nodeContains(Node node, String abstractFeature) {
		if (node instanceof Literal) {
			Literal lit = (Literal) node;
			return lit.var.equals(abstractFeature);
		}
		for (Node child : node.getChildren())
			if (nodeContains(child, abstractFeature))
				return true;
		return false;
	}

	private static Node simplify(Node node) {
		if (node instanceof Literal) {
			Literal lit = (Literal) node;
			if (lit.var.equals(varFalse) && !lit.positive)
				return new Literal(varTrue);
			if (lit.var.equals(varTrue) && !lit.positive)
				return new Literal(varFalse);
			return lit;
		}
		final Node[] children = node.getChildren();
		int removeChildren = 0;
		for (int i = 0; i < children.length; i++) {
			Node child = simplify(children[i]);
			if (child instanceof Literal) {
				Literal lit = (Literal) child;
				// we assume that litTrue and litFalse can only occur positive
				if (lit.var.equals(varTrue)) {
					if (node instanceof Not)
						return new Literal(varFalse);
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
					if (node instanceof AtMost) {
						AtMost atmost = (AtMost) node;
						if (atmost.max < 1)
							return new Literal(varFalse);
						Node[] newChildren = new Node[children.length - 1];
						for (int j = 0; j < i; j++)
							newChildren[j] = children[j];
						for (int j = i + 1; j < children.length; j++)
							newChildren[j - 1] = children[j];
						if (atmost.max > 1)
							return simplify(new AtMost(atmost.max - 1, newChildren));
						for (int j = 0; j < newChildren.length; j++) {
							Node newChild = newChildren[j];
							if (newChild instanceof Literal)
								((Literal) newChild).positive = !((Literal) newChild).positive;
							else
								newChildren[j] = new Not(newChild);
						}
						return simplify(new And(newChildren));
					}
				} else if (lit.var.equals(varFalse)) {
					if (node instanceof Not)
						return new Literal(varTrue);
					if (node instanceof And)
						return lit;
					if (node instanceof Or) {
						removeChildren++;
						child = null;
					}
					if (node instanceof Implies) {
						if (i == 0)
							return new Literal(varTrue);
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
		final int newSize = children.length - removeChildren;
		switch (newSize) {
		case 0:
			if (node instanceof And) {
				return new Literal(varTrue);
			}
			if (node instanceof Or) {
				return new Literal(varFalse);
			}
			break;
		case 1:
			if (node instanceof And || node instanceof Or) {
				for (Node child : children) {
					if (child != null) {
						return child;
					}
				}
			}
			break;
		default:
			break;
		}
		if (removeChildren == 0) {
			return node;
		}

		final Node[] newChildren = new Node[newSize];
		int i = 0;
		for (Node child : children) {
			if (child != null) {
				newChildren[i++] = child;
			}
		}
		node.setChildren(newChildren);

		return node;
	}

	private static Node replaceFeature(Node node, Object abstractFeature, Object replacement) {
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

	private static void createNodes(Collection<Node> nodes, IFeature rootFeature, IFeatureModel featureModel, boolean recursive, Map<Object, Node> replacings) {
		if (rootFeature == null || !rootFeature.getStructure().hasChildren())
			return;

		String s = getVariable(rootFeature.getName(), featureModel);

		Node[] children = new Node[rootFeature.getStructure().getChildrenCount()];
		int i = 0;
		for (IFeatureStructure rootChild : rootFeature.getStructure().getChildren()) {
			String var = getVariable(rootChild.getFeature().getName(), featureModel);
			children[i++] = new Literal(var, Literal.FeatureAttribute.CHILD);
		}
		Node definition = children.length == 1 ? children[0] : new Or(children);

		if (rootFeature.getStructure().isAnd()) {// &&
			// (!replacings.containsKey(featureModel.getOldName(rootFeature.getName()))
			// || !rootFeature.isPossibleEmpty())) {
			List<Node> manChildren = new LinkedList<>();
			for (IFeatureStructure feature : rootFeature.getStructure().getChildren())
				if (feature.isMandatory()) {
					String var = getVariable(feature.getFeature().getName(), featureModel);
					manChildren.add(new Literal(var, Literal.FeatureAttribute.CHILD));
				}

			// add constraints for all mandatory children S => (A & B)
			if (manChildren.size() == 1)
				nodes.add(new Implies(new Literal(s, Literal.FeatureAttribute.PARENT), manChildren.get(0)));
			else if (manChildren.size() > 1)
				nodes.add(new Implies(new Literal(s, Literal.FeatureAttribute.PARENT), new And(manChildren)));

			// add contraint (A | B | C) => S
			nodes.add(new Implies(definition, new Literal(s, Literal.FeatureAttribute.PARENT)));
		} else {
			// add constraint S <=> (A | B | C)
			if (replacings.get(featureModel.getRenamingsManager().getOldName(rootFeature.getName())) == null)
				nodes.add(new Equals(new Literal(s), definition));

			if (rootFeature.getStructure().isAlternative()) {
				// add constraint atmost1(A, B, C)
				if (children.length > 1)
					nodes.add(new AtMost(1, Node.clone(children)));
			}
		}

		if (recursive)
			for (IFeatureStructure feature : new LinkedList<>(rootFeature.getStructure().getChildren()))
				createNodes(nodes, feature.getFeature(), featureModel, true, replacings);
	}

	public static Map<Object, Node> calculateReplacingMap(IFeatureModel featureModel) {
		Map<Object, Node> map = new HashMap<>();
		for (IFeature feature : featureModel.getFeatures()) {
			if (feature.getStructure().isAbstract()) {
				String var = getVariable(feature.getName(), featureModel);
				Node replacing = calculateReplacing(var, featureModel);
				replacing = NodeCreator.replaceAbstractVariables(replacing, map, true);
				updateMap(map, var, replacing);
			}
		}
		return map;
	}

	public static Map<Object, Node> calculateReplacingMap(IFeatureModel featureModel, Collection<String> featureNames) {
		Map<Object, Node> map = new HashMap<>();
		for (String featureName : featureNames) {
			String var = getVariable(featureName, featureModel);
			IFeatureStructure feature = getFeature(var, featureModel).getStructure();
			Node replacing = calculateReplacing(featureModel, feature, featureNames);
			replacing = NodeCreator.replaceAbstractVariables(replacing, map, true);
			updateMap(map, var, replacing);
		}
		return map;
	}

	/**
	 * Replaces all occurrences of the given variable in values of the map.
	 */
	private static void updateMap(Map<Object, Node> map, Object var, Node replacing) {
		for (Entry<Object, Node> entry : map.entrySet()) {
			Map<Object, Node> tempMap = new HashMap<Object, Node>();
			tempMap.put(var, replacing);
			entry.setValue(NodeCreator.replaceAbstractVariables(entry.getValue(), tempMap, true));
		}
		map.put(var, replacing);
	}

	private static Node calculateReplacing(Object var, IFeatureModel featureModel) {
		IFeatureStructure feature = getFeature(var, featureModel).getStructure();
		return calculateReplacing(featureModel, feature);
	}

	private static Node calculateReplacing(IFeatureModel featureModel, IFeatureStructure feature) {
		if (!feature.hasChildren()) {
			IFeatureStructure parent = feature.getParent();
			if (parent == null || parent.isAbstract())
				return null;
			if ((parent.isAnd() && feature.isMandatorySet()) || (!parent.isAnd() && parent.getChildrenCount() == 1))
				return new Literal(featureModel.getRenamingsManager().getOldName(parent.getFeature().getName()));
			return null;
		}
		if (feature.isAnd()) {
			for (IFeatureStructure child : feature.getChildren())
				if (child.isMandatorySet() && child.isConcrete())
					return new Literal(featureModel.getRenamingsManager().getOldName(child.getFeature().getName()));
			for (IFeatureStructure child : feature.getChildren())
				if (child.isMandatorySet())
					return new Literal(featureModel.getRenamingsManager().getOldName(child.getFeature().getName()));
			return null;
		}
		List<Node> children = new LinkedList<>();
		for (IFeatureStructure child : feature.getChildren()) {
			String var2 = featureModel.getRenamingsManager().getOldName(child.getFeature().getName());
			children.add(new Literal(var2));
		}
		if (children.size() == 1)
			return children.get(0);
		return new Or(children);
	}

	private static Node calculateReplacing(IFeatureModel featureModel, IFeatureStructure feature, Collection<String> featureNames) {
		if (!feature.hasChildren()) {
			IFeatureStructure parent = feature.getParent();
			if (parent == null || featureNames.contains(parent.getFeature().getName()))
				return null;
			if ((parent.isAnd() && feature.isMandatorySet()) || (!parent.isAnd() && parent.getChildrenCount() == 1))
				return new Literal(featureModel.getRenamingsManager().getOldName(parent.getFeature().getName()));
			return null;
		}
		if (feature.isAnd()) {
			for (IFeatureStructure child : feature.getChildren())
				if (child.isMandatorySet() && !featureNames.contains(child.getFeature().getName()))
					return new Literal(featureModel.getRenamingsManager().getOldName(child.getFeature().getName()));
			for (IFeatureStructure child : feature.getChildren())
				if (child.isMandatorySet())
					return new Literal(featureModel.getRenamingsManager().getOldName(child.getFeature().getName()));
			return null;
		}
		List<Node> children = new LinkedList<>();
		for (IFeatureStructure child : feature.getChildren()) {
			String var2 = featureModel.getRenamingsManager().getOldName(child.getFeature().getName());
			children.add(new Literal(var2));
		}
		if (children.size() == 1)
			return children.get(0);
		return new Or(children);
	}

	private static IFeature getFeature(Object var, IFeatureModel featureModel) {
		String currentName = featureModel.getRenamingsManager().getNewName((String) var);
		return featureModel.getFeature(currentName);
	}

	public static String getVariable(String featureName, IFeatureModel featureModel) {
		return featureModel.getRenamingsManager().getOldName(featureName);
	}

	public static String getVariable(IFeature feature, IFeatureModel featureModel) {
		return featureModel.getRenamingsManager().getOldName(feature.getName());
	}

}
