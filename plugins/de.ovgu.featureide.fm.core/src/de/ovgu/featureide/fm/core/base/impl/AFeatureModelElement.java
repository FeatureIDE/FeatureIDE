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
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;

/**
 * Partial implementation of feature and constraint.
 * 
 * @author Sebastian Krieter
 * 
 */
public abstract class AFeatureModelElement implements IFeatureModelElement, PropertyConstants {
	
	protected final long id;

	protected final IFeatureModel featureModel;
	protected final LinkedList<PropertyChangeListener> listenerList = new LinkedList<>();
	
	protected AFeatureModelElement(AFeatureModelElement oldElement, IFeatureModel featureModel) {
		this.featureModel = featureModel != null ? featureModel : oldElement.featureModel;
		this.id = oldElement.id;
	}

	public AFeatureModelElement(IFeatureModel featureModel) {
		this.id = featureModel.getNextElementId();
		this.featureModel = featureModel;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	@Override
	public final long getId() {
		return id;
	}

	@Override
	public void propertyChange(PropertyChangeEvent evt) {

	}
	
	@Override
	public final void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener)) {
			listenerList.add(listener);
		}
	}

	@Override
	public final void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}

	@Override
	public final void fireEvent(PropertyChangeEvent event) {
		for (final PropertyChangeListener listener : listenerList) {
			listener.propertyChange(event);
		}
	}

	@Override
	public final int hashCode() {
		return (int) (37 * id);
	}

	@Override
	public final boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		AFeatureModelElement other = (AFeatureModelElement) obj;
		return id == other.id;
	}

}
