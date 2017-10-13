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
package de.ovgu.featureide.fm.core.base.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;
import javax.annotation.Nonnull;

import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureComparator;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Represents a propositional constraint below the feature diagram.
 *
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public abstract class AConstraint extends AFeatureModelElement implements IConstraint {

	protected ConstraintAttribute attribute = ConstraintAttribute.NORMAL;

	protected final Collection<IFeature> containedFeatureList = new LinkedList<>();
	protected final Collection<IFeature> deadFeatures = new LinkedList<>();

	protected final Collection<IFeature> falseOptionalFeatures = new LinkedList<>();

	protected Node propNode;
	boolean featureSelected;
	boolean isImplicit;
	protected String description;

	protected AConstraint(AConstraint oldConstraint, IFeatureModel featureModel) {
		super(oldConstraint, featureModel);
		propNode = oldConstraint.propNode;
		featureSelected = oldConstraint.featureSelected;
		isImplicit = oldConstraint.isImplicit;
		description = oldConstraint.description;
	}

	public AConstraint(IFeatureModel featureModel, Node propNode) {
		super(featureModel);
		this.propNode = propNode;
		featureSelected = false;
		isImplicit = false;
		description = "";
	}

	@Override
	public ConstraintAttribute getConstraintAttribute() {
		return attribute;
	}

	/**
	 *
	 * @return All {@link Feature}s contained at this {@link AConstraint}.
	 */
	@Override
	public Collection<IFeature> getContainedFeatures() {
		synchronized (containedFeatureList) {
			if (containedFeatureList.isEmpty()) {
				setContainedFeatures();
			}
			return containedFeatureList;
		}
	}

	@Override
	public Collection<IFeature> getDeadFeatures() {
		return Collections.unmodifiableCollection(deadFeatures);
	}

	@Override
	public Collection<IFeature> getDeadFeatures(SatSolver solver, IFeatureModel featureModel, Collection<IFeature> exlcudeFeatuers) {

		final Collection<IFeature> deadFeatures;
		final Node propNode = getNode();
		final Comparator<IFeature> featComp = new FeatureComparator(true);
		if (propNode != null) {
			deadFeatures = featureModel.getAnalyser().getDeadFeatures(solver, propNode);
		} else {
			deadFeatures = new TreeSet<IFeature>(featComp);
		}
		final Collection<IFeature> deadFeaturesAfter = new TreeSet<>(featComp);

		deadFeaturesAfter.addAll(exlcudeFeatuers);
		deadFeaturesAfter.retainAll(deadFeatures);
		return deadFeaturesAfter;
	}

	@Override
	public Collection<IFeature> getFalseOptional() {
		return falseOptionalFeatures;
	}

	@Override
	public Node getNode() {
		return propNode;
	}

	@Override
	public String getDisplayName() {
		return propNode.toString();
	}

	@Override
	public boolean hasHiddenFeatures() {
		for (final IFeature f : getContainedFeatures()) {
			if (f.getStructure().isHidden() || f.getStructure().hasHiddenParent()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void setConstraintAttribute(ConstraintAttribute attribute, boolean notifyListeners) {
		this.attribute = attribute;
		if (notifyListeners) {
			fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, Boolean.FALSE, Boolean.TRUE));
		}
	}

	/**
	 * Sets the <code>containedFeatureList</code> given by <code>propNode</code>.
	 */
	@Override
	public void setContainedFeatures() {
		synchronized (containedFeatureList) {
			containedFeatureList.clear();
			for (final String featureName : propNode.getContainedFeatures()) {
				containedFeatureList.add(featureModel.getFeature(featureName));
			}
		}
	}

	@Override
	public void setDeadFeatures(Iterable<IFeature> deadFeatures) {
		this.deadFeatures.clear();
		this.deadFeatures.addAll(Functional.toList(deadFeatures));
	}

	@Override
	public boolean setFalseOptionalFeatures(IFeatureModel featureModel, Collection<IFeature> collection) {
		falseOptionalFeatures.clear();
		falseOptionalFeatures.addAll(featureModel.getAnalyser().getFalseOptionalFeatures(collection));
		collection.removeAll(falseOptionalFeatures);
		return !falseOptionalFeatures.isEmpty();
	}

	@Override
	public void setFalseOptionalFeatures(Iterable<IFeature> foFeatures) {
		falseOptionalFeatures.clear();
		falseOptionalFeatures.addAll(Functional.toList(foFeatures));
	}

	@Override
	public void setNode(Node node) {
		propNode = node;
	}

	@Override
	public String toString() {
		return "AConstraint [propNode=" + propNode + "]";
	}

	public void setDescription(@Nonnull final String description) {
		this.description = description;
	}

	/**
	 * Returns the description
	 * 
	 * @return
	 */
	public String getDescription() {
		return description;
	}

}
