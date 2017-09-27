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
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelStructure;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * All structural information of one {@link IFeature} instance.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class FeatureModelStructure implements IFeatureModelStructure {

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((rootFeature == null) ? 0 : rootFeature.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final FeatureModelStructure other = (FeatureModelStructure) obj;
		if (correspondingFeatureModel == null) {
			if (other.correspondingFeatureModel != null) {
				return false;
			}
		}
		// else if (!correspondingFeatureModel.equals(other.correspondingFeatureModel))
		// return false;
		if (rootFeature == null) {
			if (other.rootFeature != null) {
				return false;
			}
		} else if (!rootFeature.equals(other.rootFeature)) {
			return false;
		}
		return true;
	}

	protected final IFeatureModel correspondingFeatureModel;

	protected IFeatureStructure rootFeature;

	protected boolean showHiddenFeatures = false;

	protected FeatureModelStructure(FeatureModelStructure oldStructure, IFeatureModel correspondingFeatureModel) {
		this.correspondingFeatureModel = correspondingFeatureModel != null ? correspondingFeatureModel : oldStructure.correspondingFeatureModel;

		rootFeature = oldStructure.rootFeature;
	}

	public FeatureModelStructure(IFeatureModel correspondingFeatureModel) {
		this.correspondingFeatureModel = correspondingFeatureModel;
	}

	@Override
	public IFeatureModelStructure clone(IFeatureModel newFeatureNodel) {
		return new FeatureModelStructure(this, newFeatureNodel);
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return correspondingFeatureModel;
	}

	@Override
	public Collection<IFeature> getFeaturesPreorder() {
		final List<IFeature> preorderFeatures = new LinkedList<>();
		if (rootFeature != null) {
			getFeaturesPreorder(rootFeature, preorderFeatures);
		}
		return Collections.unmodifiableCollection(preorderFeatures);
	}

	protected void getFeaturesPreorder(IFeatureStructure featureStructure, List<IFeature> preorderFeatures) {
		preorderFeatures.add(featureStructure.getFeature());
		for (final IFeatureStructure child : featureStructure.getChildren()) {
			getFeaturesPreorder(child, preorderFeatures);
		}
	}

	@Override
	public IFeatureStructure getRoot() {
		return rootFeature;
	}

	@Override
	public void setShowHiddenFeatures(boolean showHiddenFeatures) {
		this.showHiddenFeatures = showHiddenFeatures;
	}

	@Override
	public boolean hasAbstract() {
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(showHiddenFeatures)) {
			if (f.getStructure().isAbstract()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasAlternativeGroup() {
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(showHiddenFeatures)) {
			if ((f.getStructure().getChildrenCount() > 1) && f.getStructure().isAlternative()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasAndGroup() {
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(showHiddenFeatures)) {
			if ((f.getStructure().getChildrenCount() > 1) && f.getStructure().isAnd()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasConcrete() {
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(showHiddenFeatures)) {
			if (f.getStructure().isConcrete()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasHidden() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if (f.getStructure().isHidden()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasIndetHidden() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if (f.getProperty().getFeatureStatus() == FeatureStatus.INDETERMINATE_HIDDEN) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasMandatoryFeatures() {
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(showHiddenFeatures)) {
			final IFeatureStructure parent = f.getStructure().getParent();
			if ((parent != null) && parent.isAnd() && f.getStructure().isMandatory()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasOptionalFeatures() {
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(showHiddenFeatures)) {
			if (!f.equals(rootFeature.getFeature()) && (f.getStructure().getParent() != null) && f.getStructure().getParent().isAnd()
				&& !f.getStructure().isMandatory()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasOrGroup() {
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(showHiddenFeatures)) {
			if ((f.getStructure().getChildrenCount() > 1) && f.getStructure().isOr()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public int numAlternativeGroup() {
		int count = 0;
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(showHiddenFeatures)) {
			if ((f.getStructure().getChildrenCount() > 1) && f.getStructure().isAlternative()) {
				count++;
			}
		}
		return count;
	}

	@Override
	public int numOrGroup() {
		int count = 0;
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(showHiddenFeatures)) {
			if ((f.getStructure().getChildrenCount() > 1) && f.getStructure().isOr()) {
				count++;
			}
		}
		return count;
	}

	@Override
	public void replaceRoot(IFeatureStructure feature) {
		// TODO remove all features that are no children of the new root (part of a different sub tree)
		correspondingFeatureModel.deleteFeatureFromTable(rootFeature.getFeature());

		feature.setParent(null);
		rootFeature = feature;
	}

	@Override
	public void setRoot(IFeatureStructure root) {
		rootFeature = root;
	}

	private boolean existsFeatureWithStatus(FeatureStatus status) {
		for (final IFeature f : correspondingFeatureModel.getFeatureTable().values()) {
			if ((!f.getStructure().hasHiddenParent() || showHiddenFeatures)) {
				if (f.getProperty().getFeatureStatus() == status) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public boolean hasFalseOptionalFeatures() {
		return existsFeatureWithStatus(FeatureStatus.FALSE_OPTIONAL);
	}

	@Override
	public boolean hasDeadFeatures() {
		return existsFeatureWithStatus(FeatureStatus.DEAD);
	}

	@Override
	public boolean hasUnsatisfiableConstraints() {
		return existsConstraintWithAttribute(ConstraintAttribute.UNSATISFIABLE);
	}

	@Override
	public boolean hasTautologyConstraints() {
		return existsConstraintWithAttribute(ConstraintAttribute.TAUTOLOGY);
	}

	@Override
	public boolean hasDeadConstraints() {
		for (final IConstraint c : getFeatureModel().getConstraints()) {
			if ((c.getConstraintAttribute() == ConstraintAttribute.DEAD) || !c.getDeadFeatures().isEmpty()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasVoidModelConstraints() {
		return existsConstraintWithAttribute(ConstraintAttribute.VOID_MODEL);
	}

	private boolean existsConstraintWithAttribute(ConstraintAttribute attribute) {
		for (final IConstraint c : getFeatureModel().getConstraints()) {
			if (c.getConstraintAttribute() == attribute) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasRedundantConstraints() {
		return existsConstraintWithAttribute(ConstraintAttribute.REDUNDANT);
	}

}
