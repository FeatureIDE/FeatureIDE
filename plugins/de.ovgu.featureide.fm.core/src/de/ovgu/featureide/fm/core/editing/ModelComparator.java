/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * Compares two feature models based on a satisfiability solver. The result is a classification of the edit that transforms one model into the second model.
 *
 * @author Thomas Thuem
 */
public class ModelComparator {

	private final long timeout;

	private enum Strategy {
		WithoutIdenticalRules, SingleTesting, SingleTestingAborted
	};

	private final Set<Strategy> strategy = new HashSet<Strategy>();

	private IFeatureModel oldModel;

	private IFeatureModel newModel;

	private Set<String> addedFeatures;

	private Set<String> deletedFeatures;

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
		if (strategyIndex > 0) {
			strategy.add(Strategy.WithoutIdenticalRules);
		}
		if (strategyIndex > 1) {
			strategy.add(Strategy.SingleTesting);
		}
		if (strategyIndex > 2) {
			strategy.add(Strategy.SingleTestingAborted);
		}
	}

	public Comparison compare(IFeatureModel oldModel, IFeatureModel newModel) {
		this.oldModel = oldModel;
		this.newModel = newModel;
		try {
			addedFeatures = calculateAddedFeatures(oldModel, newModel);
			deletedFeatures = calculateAddedFeatures(newModel, oldModel);

			final Map<Object, Node> oldMap = NodeCreator.calculateReplacingMap(oldModel);
			final Map<Object, Node> newMap = NodeCreator.calculateReplacingMap(newModel);
			optimizeReplacingMaps(oldMap, newMap);

			oldRoot = NodeCreator.createNodes(oldModel, oldMap);
			newRoot = NodeCreator.createNodes(newModel, newMap);

			oldRoot = createFalseStatementForConcreteVariables(addedFeatures, oldRoot);
			newRoot = createFalseStatementForConcreteVariables(deletedFeatures, newRoot);

			oldRootUpdated = removeIdenticalNodes(oldRoot, newRoot);
			newRootUpdated = removeIdenticalNodes(newRoot, oldRoot);

			removedProducts = new ExampleCalculator(oldModel, timeout);
			implies = implies(oldRoot, newRootUpdated, removedProducts);

			addedProducts = new ExampleCalculator(newModel, timeout);
			isImplied = implies(newRoot, oldRootUpdated, addedProducts);

			if (implies) {
				if (isImplied) {
					result = Comparison.REFACTORING;
				} else {
					result = Comparison.GENERALIZATION;
				}
			} else if (isImplied) {
				result = Comparison.SPECIALIZATION;
			} else {
				result = Comparison.ARBITRARY;
			}
		} catch (final OutOfMemoryError e) {
			result = Comparison.OUTOFMEMORY;
		} catch (final TimeoutException e) {
			result = Comparison.TIMEOUT;
		} catch (final Exception e) {
			Logger.logError(e);
			result = Comparison.ERROR;
		}
		return result;
	}

	private Set<String> calculateAddedFeatures(IFeatureModel oldModel, IFeatureModel newModel) {
		final Set<String> addedFeatures = new HashSet<String>();
		for (final IFeature feature : newModel.getFeatures()) {
			if (feature.getStructure().isConcrete()) {
				final String name = newModel.getRenamingsManager().getOldName(feature.getName());
				final IFeature associatedFeature = oldModel.getFeature(oldModel.getRenamingsManager().getNewName(name));
				if ((associatedFeature == null) || associatedFeature.getStructure().isAbstract()) {
					addedFeatures.add(name);
				}
			}
		}
		return addedFeatures;
	}

	private void optimizeReplacingMaps(Map<Object, Node> oldMap, Map<Object, Node> newMap) {
		final List<Object> toBeRemoved = new LinkedList<Object>();
		for (final Entry<Object, Node> entry : oldMap.entrySet()) {
			final Object var = entry.getKey();
			if (newMap.containsKey(var)) {
				final Node oldRepl = entry.getValue();
				final Node newRepl = newMap.get(var);
				if ((oldRepl != null) && oldRepl.equals(newRepl)) {
					toBeRemoved.add(var);
				}
			}
		}
		for (final Object var : toBeRemoved) {
			oldMap.remove(var);
			newMap.remove(var);
		}
	}

	private Node createFalseStatementForConcreteVariables(Set<String> addedFeatures, Node node) {
		if (addedFeatures.isEmpty()) {
			return node;
		}
		final LinkedList<Node> children = new LinkedList<Node>();
		for (final Object var : addedFeatures) {
			children.add(new Literal(var, false));
		}
		return new And(node, new And(children));
	}

	/**
	 * Removes all child nodes that are contained in the reference node.
	 *
	 * @param node the node to copy and remove from
	 * @param referenceNode node that specifies what do remove
	 * @return a copy of the node where some child nodes are not existent
	 */
	private Node removeIdenticalNodes(Node node, Node referenceNode) {
		if (!strategy.contains(Strategy.WithoutIdenticalRules)) {
			return node;
		}
		final LinkedList<Node> updatedNodes = new LinkedList<Node>();
		for (final Node child : node.getChildren()) {
			if (!containedIn(child, referenceNode.getChildren())) {
				updatedNodes.add(child);
			}
		}
		return updatedNodes.isEmpty() ? null : new And(updatedNodes);
	}

	public boolean implies(Node a, Node b, ExampleCalculator example) throws TimeoutException {
		if (b == null) {
			return true;
		}

		if (!strategy.contains(Strategy.SingleTesting)) {
			final Node node = new And(a.clone(), new Not(b.clone()));
			final SatSolver solver = new SatSolver(node, timeout);
			return !solver.isSatisfiable();
		}

		example.setLeft(a);
		example.setRight(b);
		return !example.findSatisfiable(strategy.contains(Strategy.SingleTestingAborted));
	}

	private boolean containedIn(Node node, Node[] nodes) {
		for (final Node child : nodes) {
			if (node.equals(child)) {
				return true;
			}
		}
		return false;
	}

	public Configuration calculateExample(boolean added) throws TimeoutException {
		return added ? addedProducts.nextExample() : removedProducts.nextExample();
	}

	public Set<Strategy> getStrategy() {
		return strategy;
	}

	public IFeatureModel getOldModel() {
		return oldModel;
	}

	public IFeatureModel getNewModel() {
		return newModel;
	}

	public Set<String> getAddedFeatures() {
		return addedFeatures;
	}

	public Set<String> getDeletedFeatures() {
		return deletedFeatures;
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
		if (isImplied == null) {
			Logger.reportBug(278);
			return false;
		}
		return isImplied;
	}

	public Comparison getResult() {
		return result;
	}

}
