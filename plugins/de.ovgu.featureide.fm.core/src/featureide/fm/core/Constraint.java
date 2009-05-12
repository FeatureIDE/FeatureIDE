/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.core;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;

import org.prop4j.Node;

public class Constraint implements PropertyConstants {

	private FeatureModel featureModel;

	private int index;

	// private Dimension size;
	//
	// private Point location;

	public Constraint(FeatureModel featureModel, int index) {
		this.featureModel = featureModel;
		this.index = index;
	}

	public Node getNode() {
		return featureModel.getConstraint(index);
	}

	// public Dimension getSize() {
	// return size;
	// }
	//
	// public void setSize(Dimension size) {
	// this.size = size;
	// }
	//
	// public Point getLocation() {
	// return location;
	// }
	//
	// public void setLocation(Point newLocation) {
	// if (newLocation == null || newLocation.equals(location))
	// return;
	// Point oldLocation = this.location;
	// this.location = newLocation;
	// fireLocationChanged(oldLocation, newLocation);
	// }

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

	// private void fireLocationChanged(Point oldLocation, Point newLocation) {
	// PropertyChangeEvent event = new PropertyChangeEvent(this,
	// LOCATION_CHANGED, oldLocation, newLocation);
	// for (PropertyChangeListener listener : listenerList)
	// listener.propertyChange(event);
	// }

}
