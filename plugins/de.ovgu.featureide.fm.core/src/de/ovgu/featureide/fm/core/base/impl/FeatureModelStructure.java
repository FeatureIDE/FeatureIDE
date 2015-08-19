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
package de.ovgu.featureide.fm.core.base.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelStructure;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * All structural information of one {@link IFeature} instance.
 * 
 * @author Sebastian Krieter
 * 
 */
public class FeatureModelStructure implements IFeatureModelStructure {

	protected final IFeatureModel correspondingFeatureModel;

	protected IFeatureStructure rootFeature;

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
	public boolean hasAbstract() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if (f.getFeatureStructure().isAbstract()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasAlternativeGroup() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if ((f.getFeatureStructure().getChildrenCount() > 1) && f.getFeatureStructure().isAlternative()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasAndGroup() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if ((f.getFeatureStructure().getChildrenCount() > 1) && f.getFeatureStructure().isAnd()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasConcrete() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if (f.getFeatureStructure().isConcrete()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasHidden() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if (f.getFeatureStructure().isHidden()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasIndetHidden() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if (f.getFeatureProperty().getFeatureStatus() == FeatureStatus.INDETERMINATE_HIDDEN) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasMandatoryFeatures() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			final IFeatureStructure parent = f.getFeatureStructure().getParent();
			if ((parent != null) && parent.isAnd() && f.getFeatureStructure().isMandatory()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasOptionalFeatures() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if (!f.equals(rootFeature) && f.getFeatureStructure().getParent().isAnd() && !f.getFeatureStructure().isMandatory()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean hasOrGroup() {
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if ((f.getFeatureStructure().getChildrenCount() > 1) && f.getFeatureStructure().isOr()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public int numAlternativeGroup() {
		int count = 0;
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if ((f.getFeatureStructure().getChildrenCount() > 1) && f.getFeatureStructure().isAlternative()) {
				count++;
			}
		}
		return count;
	}

	@Override
	public int numOrGroup() {
		int count = 0;
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			if ((f.getFeatureStructure().getChildrenCount() > 1) && f.getFeatureStructure().isOr()) {
				count++;
			}
		}
		return count;
	}

	@Override
	public void replaceRoot(IFeatureStructure feature) {
		correspondingFeatureModel.deleteFeatureFromTable(rootFeature.getFeature());
		rootFeature = feature;
	}

	@Override
	public void setRoot(IFeatureStructure root) {
		rootFeature = root;
	}

}
