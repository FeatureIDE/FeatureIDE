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
package de.ovgu.featureide.fm.ui.editors;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.IGraphicItem;
import de.ovgu.featureide.fm.core.IGraphicItem.GraphicItem;
import de.ovgu.featureide.fm.core.base.event.PropertyConstants;

/**
 * An instance of this class represents a connection between a feature and its
 * parent. It is necessary because every figure in GEF needs a associated model.
 * 
 * @author Thomas Thuem
 *
 */
public class FeatureConnection implements PropertyConstants, IGraphicItem {
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((source == null) ? 0 : source.hashCode());
		result = prime * result + ((target == null) ? 0 : target.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FeatureConnection other = (FeatureConnection) obj;
		if (source == null) {
			if (other.source != null)
				return false;
		} else if (!source.equals(other.source))
			return false;
		if (target == null) {
			if (other.target != null)
				return false;
		} else if (!target.equals(other.target))
			return false;
		return true;
	}

	private IGraphicalFeature source;
	
	private IGraphicalFeature target;
	
	public FeatureConnection(IGraphicalFeature source) {
		this.source = source;
	}
	
	public IGraphicalFeature getSource() {
		return (IGraphicalFeature) source;
	}
	
	public IGraphicalFeature getTarget() {
		return (IGraphicalFeature) target;
	}
	
	public void setTarget(IGraphicalFeature target) {
		if (this.target == target)
			return;
		this.target = target;
		fireParentChanged();
	}

	private LinkedList<PropertyChangeListener> listenerList = new LinkedList<>();
	
	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener))
			listenerList.add(listener);
	}
	
	public void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}
	
	private void fireParentChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this, PARENT_CHANGED, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}
	
	@Override
	public String toString() {
		return source + " - " + target;
	}
	
	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Connection;
	}

}
