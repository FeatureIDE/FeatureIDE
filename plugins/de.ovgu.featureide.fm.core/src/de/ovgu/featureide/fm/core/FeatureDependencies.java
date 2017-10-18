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
package de.ovgu.featureide.fm.core;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;

/**
 * Calculates dependencies of features
 *
 * @author Soenke Holthusen
 * @author Marcus Pinnecke (Feature Interface) *
 */
public class FeatureDependencies {

	private static final String LEGEND_TEXT = "X ALWAYS Y := If X is selected then Y is selected in every valid configuration." + "\n"
		+ "X MAYBE  Y := If X is selected then Y is selected in at least one but not all valid configurations. " + "\n"
		+ "X NEVER  Y := If X is selected then Y cannot be selected in any valid configuration." + "\n";

	private final IFeatureModel fm;
	private final Node rootNode;

	private final Map<IFeature, Set<IFeature>> always = new HashMap<IFeature, Set<IFeature>>();
	private final Map<IFeature, Set<IFeature>> never = new HashMap<IFeature, Set<IFeature>>();
	private final Map<IFeature, Set<IFeature>> maybe = new HashMap<IFeature, Set<IFeature>>();

	/**
	 * @param fm
	 */
	public FeatureDependencies(IFeatureModel fm) {
		this(fm, true);
	}

	/**
	 * This constructor has the option to not calculate all dependencies automatically.
	 *
	 * @param fm The feature model
	 * @param calculateDependencies <code>true</code> if dependencies should be calculated
	 */
	public FeatureDependencies(IFeatureModel fm, boolean calculateDependencies) {
		this.fm = fm;
		rootNode = createRootNode(fm);
		if (calculateDependencies) {
			calculateDependencies();
		}
	}

	/**
	 * calculates feature dependencies
	 */
	private void calculateDependencies() {
		for (final IFeature feature : fm.getFeatures()) {
			always.put(feature, new HashSet<IFeature>());
			never.put(feature, new HashSet<IFeature>());
			maybe.put(feature, new HashSet<IFeature>());

			final Node nodeSel = new And(rootNode, new Literal(feature.getName()));

			for (final IFeature current_feature : fm.getFeatures()) {
				if (!current_feature.equals(feature)) {
					try {
						if (nodeImpliesFeature(nodeSel, current_feature.getName(), true)) {
							always.get(feature).add(current_feature);
						} else if (nodeImpliesFeature(nodeSel, current_feature.getName(), false)) {
							never.get(feature).add(current_feature);
						} else {
							maybe.get(feature).add(current_feature);
						}
					} catch (final TimeoutException e) {
						Logger.logError(e);
					}
				}
			}
		}
	}

	/**
	 * Gets all implied features of the given feature
	 *
	 * @param feature
	 * @return all implied features
	 */
	public Collection<IFeature> getImpliedFeatures(IFeature feature) {
		if (always.containsKey(feature)) {
			return always.get(feature);
		}
		always.put(feature, new HashSet<IFeature>());
		final Node nodeSel = new And(rootNode, new Literal(feature.getName()));
		final Collection<IFeature> impliedFeatures = always.get(feature);
		try {
			for (final IFeature f : fm.getFeatures()) {
				if (!f.equals(feature)) {
					if (nodeImpliesFeature(nodeSel, f.getName(), true)) {
						impliedFeatures.add(f);
					}
				}
			}
		} catch (final TimeoutException e) {
			Logger.logError(e);
		}
		return impliedFeatures;
	}

	/**
	 * @param A Feature
	 * @param B Feature
	 * @return <code>true</code> if A implies B
	 */
	public boolean isAlways(IFeature A, IFeature B) {
		if (always.containsKey(A)) {
			return always.get(A).contains(B);
		}
		final Node nodeSel = new And(rootNode, new Literal(A.getName()));
		try {
			return nodeImpliesFeature(nodeSel, B.getName(), true);
		} catch (final TimeoutException e) {
			Logger.logError(e);
		}
		return false;
	}

	/**
	 * creates the Node representation of the featureModel
	 *
	 * @param fm featureModel
	 * @return Node representing the featureModel
	 */
	private Node createRootNode(IFeatureModel fm) {
		return AdvancedNodeCreator.createCNF(fm);
	}

	/**
	 * @param node
	 * @param s
	 * @param positive if false, the feature is negated
	 * @return true if the given feature is selected in every valid configuration for the featureModel represented by node
	 * @throws TimeoutException
	 */
	private boolean nodeImpliesFeature(Node node, String featureName, boolean positive) throws TimeoutException {
		Node nodeNeg = null;
		if (positive) {
			nodeNeg = new Not((new Implies(node, new Literal(featureName))));
		} else {
			nodeNeg = new Not((new Implies(node, new Not(featureName))));
		}
		return !new SatSolver(nodeNeg, 2500).isSatisfiable();
	}

	/**
	 * @param feature
	 * @return
	 */
	public Set<IFeature> always(IFeature feature) {
		return always.get(feature);
	}

	/**
	 * @param feature
	 * @return
	 */
	public Set<IFeature> never(IFeature feature) {
		return never.get(feature);
	}

	/**
	 * @param feature
	 * @return
	 */
	public Set<IFeature> maybe(IFeature feature) {
		return maybe.get(feature);
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		for (final IFeature feature : fm.getFeatures()) {
			builder.append("\n");
			for (final IFeature f : always.get(feature)) {
				builder.append(feature.getName() + " ALWAYS " + f.getName() + "\n");
			}
			for (final IFeature f : never.get(feature)) {
				builder.append(feature.getName() + " NEVER " + f.getName() + "\n");
			}
			for (final IFeature f : maybe.get(feature)) {
				builder.append(feature.getName() + " MAYBE " + f.getName() + "\n");
			}
		}
		return builder.toString();
	}

	public String toStringWithLegend() {
		return LEGEND_TEXT + toString();
	}

}
