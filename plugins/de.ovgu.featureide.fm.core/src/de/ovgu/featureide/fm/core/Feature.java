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
import java.util.List;

/**
 * Provides all properties of a feature. This includes its connections to parent
 * and child features.
 * 
 * @author Thomas Thuem
 * 
 */
public class Feature implements PropertyConstants {

	private String name;

	private boolean mandatory = false;
	
	private boolean concret = true;

	private boolean and = true;

	private boolean multiple = false;
	
	private boolean hidden = false;

	private FeatureModel featureModel;

	public Feature(FeatureModel featureModel) {
		this.featureModel = featureModel;
		name = "Unknown";
		sourceConnections.add(parentConnection);
	}

	public Feature(FeatureModel featureModel, String name) {
		this.featureModel = featureModel;
		this.name = name;
		sourceConnections.add(parentConnection);
	}

	public boolean isAnd() {
		return and;
	}

	public boolean isOr() {
		return !and && multiple;
	}

	public boolean isAlternative() {
		return !and && !multiple;
	}

	public void changeToAnd() {
		and = true;
		multiple = false;
		fireChildrenChanged();
	}

	public void changeToOr() {
		and = false;
		multiple = true;
		fireChildrenChanged();
	}

	public void changeToAlternative() {
		and = false;
		multiple = false;
		fireChildrenChanged();
	}

	public void setAND(boolean and) {
		this.and = and;
		fireChildrenChanged();
	}

	public boolean isMandatorySet() {
		return mandatory;
	}

	public boolean isMandatory() {
		return parent == null || !parent.isAnd() || mandatory;
	}

	public void setMandatory(boolean mandatory) {
		this.mandatory = mandatory;
		fireMandantoryChanged();
	}
	
	public boolean isHidden() {
		return hidden;
	}

	public void setHidden(boolean hid) {
		this.hidden = hid;
	}
	
	public void setAbstract(Boolean value) {
		this.concret = !value;
		fireChildrenChanged();
	}

	public boolean isMultiple() {
		return multiple;
	}

	public void setMultiple(boolean multiple) {
		this.multiple = multiple;
		fireChildrenChanged();
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
		fireNameChanged();
	}

	/**
	 * Returns true if the rule can be writen in a format like 'Ab [Cd] Ef ::
	 * Gh'.
	 */
	public boolean hasInlineRule() {
		return getChildrenCount() > 1 && and && isMandatory() && !multiple;
	}

	private Feature parent;

	private LinkedList<Feature> children = new LinkedList<Feature>();

	public void setParent(Feature newParent) {
		if (newParent == parent)
			return;

		// delete old parent connection (if existing)
		if (parent != null) {
			parent.removeTargetConnection(parentConnection);
			parentConnection.setTarget(null);
		}

		// update the target
		parent = newParent;
		if (newParent != null) {
			parentConnection.setTarget(newParent);
			newParent.addTargetConnection(parentConnection);
		}
	}

	public Feature getParent() {
		return parent;
	}

	public boolean isRoot() {
		return parent == null;
	}

	public LinkedList<Feature> getChildren() {
		return children;
	}

	public void setChildren(LinkedList<Feature> children) {
		if (this.children == children)
			return;
		for (Feature child : children) {
			child.setParent(this);
		}
		this.children = children;
		fireChildrenChanged();
	}

	public boolean hasChildren() {
		return !children.isEmpty();
	}

	public void addChild(Feature newChild) {
		children.add(newChild);
		newChild.setParent(this);
		fireChildrenChanged();
	}

	public void addChildAtPosition(int index, Feature newChild) {
		children.add(index, newChild);
		newChild.setParent(this);
		fireChildrenChanged();
	}

	public void replaceChild(Feature oldChild, Feature newChild) {
		int index = children.indexOf(oldChild);
		children.set(index, newChild);
		oldChild.setParent(null);
		newChild.setParent(this);
		fireChildrenChanged();
	}

	public void removeChild(Feature child) {
		children.remove(child);
		child.setParent(null);
		fireChildrenChanged();
	}

	public Feature removeLastChild() {
		Feature child = children.removeLast();
		child.setParent(null);
		fireChildrenChanged();
		return child;
	}

	private FeatureConnection parentConnection = new FeatureConnection(this);

	private LinkedList<FeatureConnection> sourceConnections = new LinkedList<FeatureConnection>();

	private LinkedList<FeatureConnection> targetConnections = new LinkedList<FeatureConnection>();

	private static final LinkedList<FeatureConnection> EMPTY_LIST = new LinkedList<FeatureConnection>();

	public List<FeatureConnection> getSourceConnections() {
		return parent == null ? EMPTY_LIST : sourceConnections;
	}

	public List<FeatureConnection> getTargetConnections() {
		return targetConnections;
	}

	public void addTargetConnection(FeatureConnection connection) {
		targetConnections.add(connection);
	}

	public boolean removeTargetConnection(FeatureConnection connection) {
		return targetConnections.remove(connection);
	}

	//	
	// private Point location;
	//	
	// private Dimension size;
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
	//
	// public Dimension getSize() {
	// return size;
	// }
	//
	// public void setSize(Dimension size) {
	// this.size = size;
	// }
	//	
	// public Rectangle getBounds() {
	// return new Rectangle(location, size);
	// }

	private LinkedList<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();

	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener))
			listenerList.add(listener);
	}

	public void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}

	// private void fireLocationChanged(Point oldLocation, Point newLocation) {
	// PropertyChangeEvent event = new PropertyChangeEvent(this,
	// LOCATION_CHANGED, oldLocation, newLocation);
	// for (PropertyChangeListener listener : listenerList)
	// listener.propertyChange(event);
	// }

	private void fireNameChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this, NAME_CHANGED,
				false, true);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	private void fireChildrenChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				CHILDREN_CHANGED, false, true);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	private void fireMandantoryChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				MANDANTORY_CHANGED, false, true);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	// public Point getReferencePoint() {
	// return new Rectangle(location, size).getCenter();
	// }
	//
	// public Point calculateReferencePoint(Point newLocation) {
	// return new Rectangle(newLocation, size).getCenter();
	// }

	public boolean isAncestorOf(Feature next) {
		while (next.getParent() != null) {
			if (next.getParent() == this)
				return true;
			next = next.getParent();
		}
		return false;
	}

	public boolean isFirstChild(Feature child) {
		return children.indexOf(child) == 0;
	}

	public int getChildrenCount() {
		return children.size();
	}

	public Feature getFirstChild() {
		if (children.isEmpty())
			return null;
		return children.get(0);
	}

	public Feature getLastChild() {
		if (!children.isEmpty()) {
			return children.getLast();
		}
		return null;
	}

	// public Point getSourceLocation() {
	// return getSourceLocation(getBounds());
	// }
	//	
	// public Point getSourceLocation(Point newLocation) {
	// return getSourceLocation(new Rectangle(newLocation, getSize()));
	// }
	//
	// private Point getSourceLocation(Rectangle bounds) {
	// return new Point(bounds.getCenter().x, bounds.y - 1);
	// }
	//
	// public Point getTargetLocation() {
	// Rectangle bounds = getBounds();
	// return new Point(bounds.getCenter().x, bounds.bottom());
	// }

	public int getChildIndex(Feature feature) {
		return children.indexOf(feature);
	}

	public boolean isAbstract() {
		return (!this.concret);
	}

	public boolean isConcrete() {
		return this.concret;
	}

	public boolean isLayer() {
		return !isAbstract();
	}

	public boolean isANDPossible() {
		if (parent == null || parent.isAnd())
			return false;
		for (Feature child : children) {
			if (child.isAnd())
				return false;
		}
		return true;
	}

	/**
	 * used externally to fire events, eg for graphical changes not anticipated
	 * in the core implementation
	 * 
	 * @param event
	 */
	public void fire(PropertyChangeEvent event) {
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	@Override
	public Feature clone() {
		Feature feature = new Feature(featureModel, name);
		for (Feature child : children) {
			feature.addChild(child.clone());
		}
		feature.and = and;
		feature.mandatory = mandatory;
		feature.multiple = multiple;
		feature.hidden = hidden;
		feature.concret = concret;
		return feature;
	}
	
	
	public void setAnd() {
		this.and = true;
	}
	
	public void setOr() {
		this.and = false;
		this.multiple = true;
	}
	
	public void setAlternative() {
		this.and = false;
		this.multiple = false;
	}

	@Override
	public String toString() {
		return name;
	}

}
