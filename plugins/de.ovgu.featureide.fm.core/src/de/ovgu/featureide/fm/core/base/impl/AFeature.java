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

import java.beans.PropertyChangeEvent;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IGraphicalFeature;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;

/**
 * Partial implementation of the {@link IFeature} interface.
 * 
 * @author Sebastian Krieter
 * 
 */
public abstract class AFeature extends AFeatureModelElement implements IFeature {

	protected final IFeatureProperty property;
	protected final IFeatureStructure structure;
	protected final IPropertyContainer propertyContainer;

	protected String name;

	protected IGraphicalFeature graphicalRepresentation;

	protected AFeature(AFeature oldFeature, IFeatureModel featureModel, IFeatureStructure newFeatrureStructure) {
		super(oldFeature, featureModel);
		name = new String(oldFeature.name.toString());

		graphicalRepresentation = oldFeature.graphicalRepresentation;
		property = oldFeature.property.clone(this);
		structure = newFeatrureStructure != null ? newFeatrureStructure : oldFeature.structure;
		propertyContainer = createPropertyContainer();
		propertyContainer.setEntrySet(oldFeature.getCustomProperties().entrySet());
	}

	public AFeature(IFeatureModel featureModel, String name) {
		super(featureModel);
		this.name = name;

		graphicalRepresentation = createGraphicalRepresentation();
		property = createProperty();
		structure = createStructure();
		propertyContainer = createPropertyContainer();
	}

	protected IPropertyContainer createPropertyContainer() {
		return new MapPropertyContainer();
	}

	protected IGraphicalFeature createGraphicalRepresentation() {
		return GraphicMap.getInstance().getGraphicRepresentation(this);
	}

	protected IFeatureProperty createProperty() {
		return new FeatureProperty(this);
	}

	protected IFeatureStructure createStructure() {
		return new FeatureStructure(this);
	}

	@Override
	public IGraphicalFeature getGraphicRepresenation() {
		return graphicalRepresentation;
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
		this.name = name;
		final CharSequence oldName = this.name;
		fireEvent(new PropertyChangeEvent(this, NAME_CHANGED, oldName, name));
	}	

	@Override
	public IPropertyContainer getCustomProperties() {
		return propertyContainer;
	}

	@Override
	public String toString() {
//		StringBuilder sb = new StringBuilder("name=" + name);
//		sb.append(", Structure=[");
//		FeatureUtils.print(this, sb);
//		sb.append("]");
//		return "Feature(" + sb.toString() + ")";
		return getName();
	}

}
