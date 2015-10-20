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
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
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
	
	private static long NEXT_ID = 0;
	
	protected static final synchronized long getNextId() {
		return NEXT_ID++;
	}

	private final long id;

	protected IFeatureModel featureModel;
	protected LinkedList<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();

	protected CharSequence name;

	protected final IFeatureProperty property;
	protected final IFeatureStructure structure;
	protected IGraphicalFeature graphicalRepresentation;
	private boolean constraintSelected;

	protected Feature(Feature oldFeature, IFeatureModel featureModel, IFeatureStructure newFeatrureStructure) {
		this.featureModel = featureModel != null ? featureModel : oldFeature.featureModel;
		this.id = oldFeature.id;
		name = new String(oldFeature.name.toString());
		graphicalRepresentation = oldFeature.graphicalRepresentation;
		constraintSelected = oldFeature.constraintSelected;

		property = oldFeature.property.clone(this);
		structure = newFeatrureStructure != null ? newFeatrureStructure : oldFeature.structure;

	}

	public Feature(IFeatureModel featureModel, CharSequence name) {
		this.id = getNextId();
		this.featureModel = featureModel;
		this.name = name;
		this.constraintSelected = false;

		property = createProperty();
		structure = createStructure();
		graphicalRepresentation = createGraphicalRepresentation();
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
	public long getId() {
		return id;
	}

	@Override
	public String getName() {
		return name.toString();
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
		final CharSequence oldName = this.name;
		this.name = name;
		fireEvent(new PropertyChangeEvent(this, NAME_CHANGED, oldName, name));
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder("name=" + name);
		sb.append(", Structure=[");
		FeatureUtils.print(this, sb);
		sb.append("]");
		return "Feature(" + sb.toString() + ")";
	}

	@Override
	public IGraphicalFeature getGraphicRepresenation() {
		return graphicalRepresentation;
	}

	@Override
	public boolean isConstraintSelected() {
		return constraintSelected;
	}

	@Override
	public void setConstraintSelected(boolean b) {
		constraintSelected = b;
	}

//	@Override
//	public int hashCode() {
//		//		final int prime = 31;
//		//		int result = 1;
//		//		result = prime * result + ((name == null) ? 0 : name.hashCode());
//		return (name == null) ? 0 : name.hashCode();
//	}
//
//	@Override
//	public boolean equals(Object obj) {
//		if (this == obj)
//			return true;
//		if (obj == null || getClass() != obj.getClass())
//			return false;
//		Feature other = (Feature) obj;
//		return (name != null && name.equals(other.name));
//	}

	@Override
	public int hashCode() {
		return (int) (37 * id);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		Feature other = (Feature) obj;
		return id == other.id;
	}

}
