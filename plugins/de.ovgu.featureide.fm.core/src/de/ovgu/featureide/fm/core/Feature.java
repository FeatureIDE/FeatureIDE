/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * Provides all properties of a feature. This includes its connections to parent
 * and child features.
 * 
 * @author Thomas Thuem
 * 
 */
public class Feature implements PropertyConstants, PropertyChangeListener {

	private String name;

	private boolean mandatory = false;

	private boolean concret = true;

	private boolean and = true;

	private boolean multiple = false;

	private boolean hidden = false;

	private boolean constraintSelected = false;

	private ColorList colorList;

	private List<Constraint> partOfConstraints = new ArrayList<Constraint>();

	private FeatureStatus status = FeatureStatus.NORMAL;

	private FeatureModel featureModel;

	private FMPoint location = new FMPoint(0, 0);

	public Feature(FeatureModel featureModel) {
		this.featureModel = featureModel;
		name = "Unknown";
		sourceConnections.add(parentConnection);
		colorList = new ColorList(this);
	}

	public Feature(FeatureModel featureModel, String name) {
		this.featureModel = featureModel;
		this.name = name;
		sourceConnections.add(parentConnection);
		colorList = new ColorList(this);
	}

	public void setNewLocation(FMPoint newLocation) {
		location = newLocation;
	}

	public FMPoint getLocation() {
		return location;
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
		fireMandatoryChanged();
	}

	public boolean isHidden() {
		return hidden;
	}

	public void setHidden(boolean hid) {
		this.hidden = hid;
		fireHiddenChanged();
	}

	public boolean isConstraintSelected() {
		return constraintSelected;
	}

	public void setConstraintSelected(boolean selection) {
		this.constraintSelected = selection;
		fire(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, Boolean.FALSE,
				Boolean.TRUE));
	}

	public void setAbstract(boolean value) {
		this.concret = !value;
		fireChildrenChanged();
	}

	public List<Constraint> getRelevantConstraints() {
		return partOfConstraints;
	}

	public void setRelevantConstraints() {
		List<Constraint> constraintList = new ArrayList<Constraint>();

		for (Constraint constraint : featureModel.getConstraints()) {
			if (constraint.toString().contains(this.getName()))
				constraintList.add(constraint);
		}

		this.partOfConstraints = constraintList;
	}

	public FeatureStatus getFeatureStatus() {
		return status;
	}

	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	public void setFeatureStatus(FeatureStatus stat, boolean fire) {
		this.status = stat;
		if (fire)
			fire(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED,
					Boolean.FALSE, Boolean.TRUE));
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
				Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	private void fireHiddenChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				HIDDEN_CHANGED, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	private void fireChildrenChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				CHILDREN_CHANGED, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	private void fireMandatoryChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				MANDATORY_CHANGED, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	// private void fireColorChanged(int oldValue, int newValue) {
	// PropertyChangeEvent event = new PropertyChangeEvent(this, COLOR_CHANGED,
	// oldValue, newValue);
	// for (PropertyChangeListener listener : listenerList)
	// listener.propertyChange(event);
	// }

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

	@SuppressWarnings("unchecked")
	@Override
	public Feature clone() {
		Feature feature = new Feature(featureModel, name);
		for (Feature child : (LinkedList<Feature>) children.clone()) {
			feature.addChild(child.clone());
		}
		feature.and = and;
		feature.mandatory = mandatory;
		feature.multiple = multiple;
		feature.hidden = hidden;
		feature.concret = concret;
		feature.colorList = colorList.clone(feature);
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

	public boolean hasHiddenParent() {

		if (isHidden())
			return true;
		if (isRoot()) {

			return false;
		}
		Feature p = getParent();

		while (!p.isRoot()) {
			if (p.isHidden())
				return true;
			p = p.getParent();

		}

		return false;
	}

	@Override
	public String toString() {
		return name;
	}

	@Override
	public void propertyChange(PropertyChangeEvent event) {

	}

	@Deprecated
	public String toString(boolean writeMarks) {
		if (writeMarks) {
			if (this.name.contains(" ") || Operator.isOperatorName(this.name)) {
				return "\"" + this.name + "\"";
			}
			return name;
		} else {
			return toString();
		}
	}



	public ColorList getColorList() {
		return colorList;
	}

	/*
	 * auto-generated methods cause the diagram to be shown incorrectly
	 */
	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 * 
	 * @Override public int hashCode() { final int prime = 31; int result = 1;
	 * result = prime * result + (and ? 1231 : 1237); result = prime * result +
	 * ((children == null) ? 0 : children.hashCode()); result = prime * result +
	 * (concret ? 1231 : 1237); result = prime * result + (hidden ? 1231 :
	 * 1237); result = prime * result + (mandatory ? 1231 : 1237); result =
	 * prime * result + (multiple ? 1231 : 1237); result = prime * result +
	 * ((name == null) ? 0 : name.hashCode()); result = prime * result +
	 * ((parent == null) ? 0 : parent.hashCode()); return result; }
	 * 
	 * /* (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 * 
	 * @Override public boolean equals(Object obj) { if (this == obj) return
	 * true; if (obj == null) return false; if (getClass() != obj.getClass())
	 * return false; Feature other = (Feature) obj; if (and != other.and) return
	 * false; if (children == null) { if (other.children != null) return false;
	 * } else if (!children.equals(other.children)) return false; if (concret !=
	 * other.concret) return false; if (hidden != other.hidden) return false; if
	 * (mandatory != other.mandatory) return false; if (multiple !=
	 * other.multiple) return false; if (name == null) { if (other.name != null)
	 * return false; } else if (!name.equals(other.name)) return false; if
	 * (parent == null) { if (other.parent != null) return false; } else if
	 * (!parent.equals(other.parent)) return false; return true; }
	 */

}