/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;

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

	protected final IPropertyContainer propertyContainer;

	protected final List<IFeature> containedFeatureList = new ArrayList<>();

	protected Node propNode;
	boolean featureSelected;
	boolean isImplicit;
	protected String description;
	/**
	 * Stores the tags of the constraint this group belongs to.
	 */
	protected final Set<String> tags;

	/**
	 * Creates a copy of <code>oldConstraint</code> that belongs to <code>featureModel</code>.
	 *
	 * @param oldConstraint - {@link IConstraint}
	 * @param featureModel - {@link IFeatureModel}
	 * @param copyId - If <code>true</code> the id of the old constraint is kept. Otherwise a new id is assigned to the new constraint.
	 */
	public AConstraint(IConstraint oldConstraint, IFeatureModel featureModel, boolean copyId) {
		super(oldConstraint, featureModel, copyId);
		setNode(oldConstraint.getNode().clone());
		description = oldConstraint.getDescription();
		tags = new HashSet<>(oldConstraint.getTags());
		propertyContainer = new MapPropertyContainer(oldConstraint.getCustomProperties());
		if (oldConstraint instanceof AConstraint) {
			final AConstraint constraint = (AConstraint) oldConstraint;
			featureSelected = constraint.featureSelected;
			isImplicit = constraint.isImplicit;
		}
	}

	/**
	 * Creates a new {@link AConstraint} for <code>featureModel</code> that has <code>propNode</code> as formula.
	 *
	 * @param featureModel - {@link IFeatureModel}
	 * @param propNode - {@link Node}
	 */
	public AConstraint(IFeatureModel featureModel, Node propNode) {
		super(featureModel);
		setNode(propNode);
		featureSelected = false;
		isImplicit = false;
		description = "";
		tags = new HashSet<>();
		propertyContainer = new MapPropertyContainer();
	}

	@Override
	public IPropertyContainer getCustomProperties() {
		return propertyContainer;
	}

	/**
	 *
	 * @return All {@link Feature}s contained at this {@link AConstraint}.
	 */
	@Override
	public Collection<IFeature> getContainedFeatures() {
		synchronized (containedFeatureList) {
			return new ArrayList<>(containedFeatureList);
		}
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
	public void setNode(Node node) {
		propNode = node;
		synchronized (containedFeatureList) {
			containedFeatureList.clear();
			if (propNode != null) {
				for (final String featureName : propNode.getContainedFeatures()) {
					containedFeatureList.add(featureModel.getFeature(featureName));
				}
			}
		}
	}

	@Override
	public String toString() {
		return "AConstraint [propNode=" + propNode + "]";
	}

	@Override
	public void setDescription(final String description) {
		this.description = description;
	}

	@Override
	public String getDescription() {
		return description;
	}

	@Override
	public Set<String> getTags() {
		synchronized (tags) {
			return new HashSet<>(tags);
		}
	}

	@Override
	public void setTags(Set<String> tags) {
		synchronized (this.tags) {
			this.tags.clear();
			this.tags.addAll(tags);
		}
	}
}
