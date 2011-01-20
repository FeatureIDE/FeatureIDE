/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;

import org.prop4j.Node;

/**
 * Represents a propositional constraint below the feature diagram.
 * 
 * @author Thomas Thuem
 */
public class Constraint implements PropertyConstants {

	private FeatureModel featureModel;
	private Node propNode;
	

	public Constraint(FeatureModel featureModel, Node propNode) {
		this.featureModel = featureModel;
		this.propNode = propNode;
	}

	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	public Node getNode() {
		return propNode;
	}

	private LinkedList<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();

	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener))
			listenerList.add(listener);
	}

	public void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}

	public void fire(PropertyChangeEvent event) {
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}
	
	@Override
	public boolean equals(Object obj){
		
		
			if (this == obj)
				return true;
			if (!(obj instanceof Constraint))
				return false;

			Constraint other = (Constraint) obj;

		
		return propNode.equals(other.propNode);
		
	}
}
