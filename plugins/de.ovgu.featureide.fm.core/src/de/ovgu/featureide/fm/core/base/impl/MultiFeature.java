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

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IMultiFeatureModelElement;

/**
 * Feature for the {@link MultiFeatureModel}.
 *
 * @author Sebastian Krieter
 */
public class MultiFeature extends Feature implements IMultiFeatureModelElement {

	private int type = IMultiFeatureModelElement.TYPE_INTERN;
	private String externalModelName = null;
	private boolean newDefined = false;

	public MultiFeature(IFeatureModel featureModel, String name) {
		super(featureModel, name);
	}

	public MultiFeature(MultiFeature extendedFeature, IFeatureModel newFeatureModel, IFeatureStructure newStructure) {
		super(extendedFeature, newFeatureModel, newStructure);
		type = extendedFeature.type;
		externalModelName = extendedFeature.externalModelName;
		newDefined = extendedFeature.newDefined;
	}

	@Override
	protected IFeatureProperty createProperty() {
		return new MultiFeatureProperty(this);
	}

	@Override
	public int getType() {
		return type;
	}

	@Override
	public void setType(int type) {
		this.type = type;
	}

	public String getExternalModelName() {
		return externalModelName;
	}

	public void setExternalModelName(String externalModelName) {
		this.externalModelName = externalModelName;
	}

	public boolean isNewDefined() {
		return newDefined;
	}

	public void setNewDefined(boolean newDefined) {
		this.newDefined = newDefined;
	}

	@Override
	public IFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure) {
		return new MultiFeature(this, newFeatureModel, newStructure);
	}

}
