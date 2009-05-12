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
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.configuration.Configuration;

public class ModelComparator {
	
	private long timeout;
	
	private enum Strategy {WithoutIdenticalRules, SingleTesting, SingleTestingAborted};
	
	private Set<Strategy> strategy = new HashSet<Strategy>();
	
	private FeatureModel oldModel;

	private FeatureModel newModel;
	
	private Set<String> addedFeatures;

	private Set<String> deletedFeatures;

	private Set<String> replaceFeatures;

	private Node oldRoot;

	private Node newRoot;

	private Node oldRootUpdated;

	private Node newRootUpdated;

	private Boolean implies;

	private Boolean isImplied;
	
	private Comparison result;
	
	private ExampleCalculator addedProducts;
	
	private ExampleCalculator removedProducts;
	
	public ModelComparator(long timeout) {
		this(timeout, 3);
	}

	public ModelComparator(long timeout, int strategyIndex) {
		this.timeout = timeout;
		if (strategyIndex > 0)
			strategy.add(Strategy.WithoutIdenticalRules);
		if (strategyIndex > 1)
			strategy.add(Strategy.SingleTesting);
		if (strategyIndex > 2)
			strategy.add(Strategy.SingleTestingAborted);
	}

	public Comparison compare(FeatureModel oldModel, FeatureModel newModel) {
		this.oldModel = oldModel;
		this.newModel = newModel;
		try {
			addedFeatures = calculateAddedFeatures(oldModel, newModel);
			deletedFeatures = calculateAddedFeatures(newModel, oldModel);
			replaceFeatures = calculateReplaceFeatures(oldModel, deletedFeatures, newModel, addedFeatures);

			oldRoot = createNodes(oldModel, replaceFeatures);
			newRoot = createNodes(newModel, replaceFeatures);
			
			oldRoot = createFalseStatementForConcreteVariables(addedFeatures, oldRoot);
			newRoot = createFalseStatementForConcreteVariables(deletedFeatures, newRoot);

			oldRootUpdated = removeIdenticalNodes(oldRoot, newRoot);
			newRootUpdated = removeIdenticalNodes(newRoot, oldRoot);

			removedProducts = new ExampleCalculator(oldModel, timeout);
			implies = implies(oldRoot, newRootUpdated, removedProducts);

			addedProducts = new ExampleCalculator(newModel, timeout);
			isImplied = implies(newRoot, oldRootUpdated, addedProducts);

			if (implies)
				if (isImplied) 
					result = Comparison.REFACTORING;
				else 
					result = Comparison.GENERALIZATION;
			else
				if (isImplied) 
					result = Comparison.SPECIALIZATION;
				else 
					result = Comparison.ARBITRARY;
		} catch (OutOfMemoryError e) {
			result = Comparison.OUTOFMEMORY;
		} catch (TimeoutException e) {
			result = Comparison.TIMEOUT;
		} catch (Exception e) {
			e.printStackTrace();
			result = Comparison.ERROR;
		}
		return result;
	}

	private Node createNodes(FeatureModel featureModel, Set<String> replaceFeatures) {
		HashMap<Object, Node> replacingMap = calculateReplacingMap(replaceFeatures, featureModel);
		return NodeCreator.createNodes(featureModel, replacingMap);
	}

	private Set<String> calculateAddedFeatures(FeatureModel oldModel,
			FeatureModel newModel) {
		Set<String> addedFeatures = new HashSet<String>();
		for (Feature feature : newModel.getFeatures())
		    if (feature.isConcrete()) {
				String name = newModel.getOldName(feature.getName());
				Feature associatedFeature = oldModel.getFeature(oldModel.getNewName(name));
				if (associatedFeature == null || associatedFeature.isAbstract())
					addedFeatures.add(name);
			}
		return addedFeatures;
	}

	private Set<String> calculateReplaceFeatures(FeatureModel oldModel,
			Set<String> deletedFeatures, FeatureModel newModel,
			Set<String> addedFeatures) {
		Set<String> replaceFeatures = new HashSet<String>();
		addReplaceFeatures(oldModel, newModel, replaceFeatures);
		addReplaceFeatures(newModel, oldModel, replaceFeatures);
		return replaceFeatures;
	}

	private void addReplaceFeatures(FeatureModel oldModel,
			FeatureModel newModel, Set<String> replaceFeatures) {
		if (oldModel.hasAbstractFeatures())
			for (Feature feature : oldModel.getFeatures()) {
				String name = oldModel.getOldName(feature.getName());
				Feature otherFeature = newModel.getFeature(newModel.getNewName(name));
				if (feature.isAbstract() && !replaceFeatures.contains(name)) {
					if (otherFeature == null || otherFeature.isLayer())
						replaceFeatures.add(name);
					else {
						Node a = calculateReplacing(name, oldModel);
						Node b = calculateReplacing(name, newModel);
						if (!a.equals(b))
							replaceFeatures.add(name);
					}
				}
			}
	}

	private Node createFalseStatementForConcreteVariables(Set<String> addedFeatures, Node node) {
		LinkedList<Node> children = new LinkedList<Node>();
		for (Object var : addedFeatures)
			children.add(new Literal((String) var, false));
		return new And(node, new And(children));
	}

	/**
	 * Removes all child nodes that are contained in the reference node.
	 * 
	 * @param  node  the node to copy and remove from
	 * @param  referenceNode  node that specifies what do remove
	 * @return a copy of the node where some child nodes are not existent
	 */
	private Node removeIdenticalNodes(Node node, Node referenceNode) {
		if (!strategy.contains(Strategy.WithoutIdenticalRules))
			return node;
		LinkedList<Node> updatedNodes = new LinkedList<Node>();
		for (Node child : node.getChildren())
			if (!containedIn(child, referenceNode.getChildren()))
				updatedNodes.add(child);
		return updatedNodes.isEmpty() ? null : new And(updatedNodes);
	}

	private boolean implies(Node a, Node b, ExampleCalculator example) throws TimeoutException {
		if (b == null)
			return true;
		
		if (!strategy.contains(Strategy.SingleTesting)) {
			Node node = new And(a.clone(), new Not(b.clone()));
			SatSolver solver = new SatSolver(node, timeout);
			boolean valid = !solver.isSatisfiable();
			return valid;
		}
		
		example.setLeft(a);
		example.setRight(b);
		return !example.findSatisfiable(strategy.contains(Strategy.SingleTestingAborted));
	}

	private boolean containedIn(Node node, Node[] nodes) {
		for (Node child : nodes)
			if (node.equals(child))
				return true;
		return false;
	}
	
	private HashMap<Object, Node> calculateReplacingMap(Set<String> replaceFeatures, FeatureModel featureModel) {
		HashMap<Object, Node> map = new HashMap<Object, Node>();
		for (Object var : replaceFeatures) {
			Feature feature = getFeature(var, featureModel);
			if (feature != null) {
				Node replacing = calculateReplacing(var, featureModel);
				replacing = NodeCreator.eliminateAbstractVariables(replacing, map);
				updateMap(map, var, replacing);
			}
		}
		return map;
	}

	/**
	 * Replaces all occurrences of the given variable in values of the map. 
	 */
	private static void updateMap(HashMap<Object, Node> map, Object var, Node replacing) {
		for (Object key : map.keySet()) {
			Node value = map.get(key);
			HashMap<Object, Node> tempMap = new HashMap<Object, Node>();
			tempMap.put(var, replacing);
			value = NodeCreator.eliminateAbstractVariables(value, tempMap);
			map.put(key, value);
		}
		map.put(var, replacing);
	}

	public static Node calculateReplacing(Object var, FeatureModel featureModel) {
		Feature feature = getFeature(var, featureModel);
		return calculateReplacing(featureModel, feature);
	}

	private static Node calculateReplacing(FeatureModel featureModel,
			Feature feature) {
		LinkedList<Node> children = new LinkedList<Node>();
		for (Feature child : feature.getChildren()) {
			String var2 = featureModel.getOldName(child.getName());
			children.add(new Literal(var2));
		}
		if (children.size() == 1)
			return children.getFirst();
		return new Or(children);
	}

	private static Feature getFeature(Object var, FeatureModel featureModel) {
		String currentName = featureModel.getNewName((String) var);
		return featureModel.getFeature(currentName);
	}
	
	public Configuration calculateExample(boolean added) throws TimeoutException {
		return added ? addedProducts.nextExample() : removedProducts.nextExample();
	}
	
	public Set<Strategy> getStrategy() {
		return strategy;
	}

	public FeatureModel getOldModel() {
		return oldModel;
	}

	public FeatureModel getNewModel() {
		return newModel;
	}

	public Set<String> getAddedFeatures() {
		return addedFeatures;
	}

	public Set<String> getDeletedFeatures() {
		return deletedFeatures;
	}

	public Set<String> getReplaceFeatures() {
		return replaceFeatures;
	}

	public Node getOldRoot() {
		return oldRoot;
	}

	public Node getNewRoot() {
		return newRoot;
	}

	public Node getOldRootUpdated() {
		return oldRootUpdated;
	}

	public Node getNewRootUpdated() {
		return newRootUpdated;
	}

	public boolean isImplies() {
		return implies;
	}

	public boolean isImplied() {
		return isImplied;
	}

	public Comparison getResult() {
		return result;
	}

}
