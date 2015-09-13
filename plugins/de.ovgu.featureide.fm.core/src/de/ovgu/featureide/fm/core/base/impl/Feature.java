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
import java.beans.PropertyChangeListener;
import java.util.Collection;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IGraphicalFeature;

/**
 * Provides all properties of a feature. This includes its connections to parent
 * and child features.
 * 
 * @author Thomas Thuem
 * @author Sebastian Krieter
 * 
 */
public class Feature implements IFeature, PropertyConstants {

	protected IFeatureModel featureModel;
	protected LinkedList<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();

	protected CharSequence name;

	protected final IFeatureProperty property;
	protected final IFeatureStructure structure;

	protected Feature(Feature oldFeature, IFeatureModel featureModel, IFeatureStructure newFeatrureStructure) {
		this.featureModel = featureModel != null ? featureModel : oldFeature.featureModel;
		name = new String(oldFeature.name.toString());

		property = oldFeature.property.clone(this);
		structure = newFeatrureStructure != null ? newFeatrureStructure : oldFeature.structure;
	}

	public Feature(IFeatureModel featureModel, CharSequence name) {
		this.featureModel = featureModel;
		this.name = name;

		property = createProperty();
		structure = createStructure();
	}
	
	protected IFeatureProperty createProperty() {
		return new FeatureProperty(this);
	}
	
	protected IFeatureStructure createStructure() {
		return new FeatureStructure(this);
	}

	@Override
	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener)) {
			listenerList.add(listener);
		}
	}

	@Override
	public IFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure) {
		return new Feature(this, newFeatureModel, newStructure);
	}

	@Override
	public void fireEvent(PropertyChangeEvent event) {
		for (final PropertyChangeListener listener : listenerList) {
			listener.propertyChange(event);
		}
	}

	protected void fireNameChanged() {
		fireEvent(new PropertyChangeEvent(this, NAME_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return featureModel;
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
	public int getId() {
		return 0;
	}

	@Override
	public CharSequence getName() {
		return name;
	}

	@Override
	public int hashCode() {
		return name.hashCode();
	}

	@Override
	public void propertyChange(PropertyChangeEvent evt) {

	}

	@Override
	public void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}

	@Override
	public void setName(CharSequence name) {
		this.name = name;
		fireNameChanged();
	}

	@Override
	public String toString() {
		return name.toString();
	}

	@Override
	public IGraphicalFeature getGraphicRepresenation() {
		throw new UnsupportedOperationException("Not implemented yet");
	}

}
