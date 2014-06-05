/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;

/**
 * An instance of this class represents a connection between a feature and its
 * parent. It is necessary because every figure in GEF needs a associated model.
 * 
 * @author Thomas Thuem
 *
 */
public class FeatureConnection implements PropertyConstants {
	
	private Feature source;
	
	private Feature target;
	
	public FeatureConnection(Feature source) {
		this.source = source;
	}
	
	public Feature getSource() {
		return source;
	}
	
	public Feature getTarget() {
		return target;
	}
	
	public void setTarget(Feature target) {
		if (this.target == target)
			return;
		this.target = target;
		fireParentChanged();
	}

	private LinkedList<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();
	
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
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return source + " - " + target;
	}

}
