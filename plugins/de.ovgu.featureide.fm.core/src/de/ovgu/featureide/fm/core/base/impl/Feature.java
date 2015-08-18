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

import static de.ovgu.featureide.fm.core.localization.StringTable.UNKNOWN;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Provides all properties of a feature. This includes its connections to parent
 * and child features.
 * 
 * @author Thomas Thuem
 * @author Sebastian Krieter
 * 
 */
public class Feature implements IFeature, PropertyConstants {

	private final IFeatureProperty property;
	private final IFeatureStructure structure;

	private LinkedList<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();

	private IFeatureModel featureModel;
	private String name;

	public Feature(IFeatureModel featureModel) {
		this(featureModel, UNKNOWN);
	}

	public Feature(IFeatureModel featureModel, String name) {
		this.featureModel = featureModel;
		this.name = name;

		this.property = FeatureModelFactory.getInstance().createFeatureProperty(this);
		this.structure = FeatureModelFactory.getInstance().createFeatureStructure(this);
	}

	protected Feature(IFeature feature, IFeatureModel featureModel) {
		this.featureModel = featureModel;

		this.name = feature.getName();

		this.property = feature.getFeatureProperty().clone(this);
		this.structure = feature.getFeatureStructure().clone(this);
	}

	@Override
	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener))
			listenerList.add(listener);
	}

	@Override
	public void fireEvent(PropertyChangeEvent event) {
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);

	}

	private void fireNameChanged() {
		fireEvent(new PropertyChangeEvent(this, NAME_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	@Override
	public IFeatureProperty getFeatureProperty() {
		return property;
	}

	@Override
	public IFeatureStructure getFeatureStructure() {
		return structure;
	}

	@Override
	public int getId() {
		return 0;
	}

	@Override
	public String getName() {
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

	public void setName(String name) {
		this.name = name;
		fireNameChanged();
	}

	@Override
	public String toString() {
		return name;
	}
}
