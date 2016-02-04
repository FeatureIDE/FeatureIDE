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

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * Partial implementation of the {@link IFeature} interface.
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public abstract class AFeature extends AFeatureModelElement implements IFeature {

	protected final IFeatureProperty property;
	protected final IFeatureStructure structure;
	protected final IPropertyContainer propertyContainer;

	protected AFeature(AFeature oldFeature, IFeatureModel featureModel, IFeatureStructure newFeatrureStructure) {
		super(oldFeature, featureModel);

		property = oldFeature.property.clone(this);
		structure = newFeatrureStructure != null ? newFeatrureStructure : oldFeature.structure;
		propertyContainer = createPropertyContainer();
		propertyContainer.setEntrySet(oldFeature.getCustomProperties().entrySet());
	}

	public AFeature(IFeatureModel featureModel, String name) {
		super(featureModel);
		this.name = name;

		property = createProperty();
		structure = createStructure();
		propertyContainer = createPropertyContainer();
	}

	protected IPropertyContainer createPropertyContainer() {
		return new MapPropertyContainer();
	}

	protected IFeatureProperty createProperty() {
		return new FeatureProperty(this);
	}

	protected IFeatureStructure createStructure() {
		return new FeatureStructure(this);
	}

	@Override
	public IFeatureProperty getProperty() {
		return property;
	}

	@Override
	public IFeatureStructure getStructure() {
		return structure;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public void setName(String name) {
		final String oldName = this.name;
		super.setName(name);
		fireEvent(new FeatureIDEEvent(this, EventType.FEATURE_NAME_CHANGED, oldName, name));
	}	

	@Override
	public IPropertyContainer getCustomProperties() {
		return propertyContainer;
	}

	@Override
	public String toString() {
		return getName();
	}

}
