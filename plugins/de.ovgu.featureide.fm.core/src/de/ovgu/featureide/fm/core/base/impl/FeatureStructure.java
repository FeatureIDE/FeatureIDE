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
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;

import de.ovgu.featureide.fm.core.FeatureConnection;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * All structural information of an {@link IFeatureModel}.
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke  
 */
public class FeatureStructure implements IFeatureStructure, PropertyConstants {


	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((children == null) ? 0 : children.hashCode());
		result = prime * result + ((correspondingFeature == null) ? 0 : correspondingFeature.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FeatureStructure other = (FeatureStructure) obj;
		if (children == null) {
			if (other.children != null)
				return false;
		} else if (!children.equals(other.children))
			return false;
		if (correspondingFeature == null) {
			if (other.correspondingFeature != null)
				return false;
		} else if (!correspondingFeature.equals(other.correspondingFeature))
			return false;
		return true;
	}

	protected boolean and;

	protected final LinkedList<IFeatureStructure> children = new LinkedList<>();
	protected boolean concrete;
	protected final IFeature correspondingFeature;

	protected boolean hidden;

	protected boolean mandatory;
	protected boolean multiple;

	protected IFeatureStructure parent = null;
	protected final FeatureConnection parentConnection;
	protected List<IConstraint> partOfConstraints = new LinkedList<>();
	protected final LinkedList<FeatureConnection> sourceConnections = new LinkedList<FeatureConnection>();
	protected final LinkedList<FeatureConnection> targetConnections = new LinkedList<FeatureConnection>();

	protected FeatureStructure(FeatureStructure oldStructure, IFeatureModel newFeatureModel) {
		if (newFeatureModel != null) {
			correspondingFeature = oldStructure.correspondingFeature.clone(newFeatureModel, this);
			newFeatureModel.addFeature(correspondingFeature);
		} else {
			correspondingFeature = oldStructure.correspondingFeature;
		}

		mandatory = oldStructure.mandatory;
		concrete = oldStructure.concrete;
		and = oldStructure.and;
		multiple = oldStructure.multiple;
		hidden = oldStructure.hidden;

		parentConnection = new FeatureConnection(correspondingFeature);
		sourceConnections.add(parentConnection);

		for (final IFeatureStructure child : oldStructure.children) {
			addNewChild(child.cloneSubtree(newFeatureModel));
		}
	}

	public FeatureStructure(IFeature correspondingFeature) {
		this.correspondingFeature = correspondingFeature;

		mandatory = false;
		concrete = true;
		and = true;
		multiple = false;
		hidden = false;

		parentConnection = new FeatureConnection(this.correspondingFeature);
		sourceConnections.add(parentConnection);
	}

	@Override
	public void addChild(IFeatureStructure newChild) {
		addNewChild(newChild);
		fireChildrenChanged();
	}

	@Override
	public void addChildAtPosition(int index, IFeatureStructure newChild) {
		children.add(index, newChild);
		newChild.setParent(this);
		fireChildrenChanged();
	}

	protected void addNewChild(IFeatureStructure newChild) {
		children.add(newChild);
		newChild.setParent(this);
	}

	@Override
	public void addTargetConnection(FeatureConnection connection) {
		targetConnections.add(connection);
	}

	@Override
	public void changeToAlternative() {
		and = false;
		multiple = false;
		fireChildrenChanged();
	}

	@Override
	public void changeToAnd() {
		and = true;
		multiple = false;
		fireChildrenChanged();
	}

	@Override
	public void changeToOr() {
		and = false;
		multiple = true;
		fireChildrenChanged();
	}

	@Override
	public IFeatureStructure cloneSubtree(IFeatureModel newFeatureModel) {
		return new FeatureStructure(this, newFeatureModel);
	}

	protected void fireChildrenChanged() {
		final PropertyChangeEvent event = new PropertyChangeEvent(this, CHILDREN_CHANGED, Boolean.FALSE, Boolean.TRUE);
		correspondingFeature.fireEvent(event);
	}

	protected void fireHiddenChanged() {
		final PropertyChangeEvent event = new PropertyChangeEvent(this, HIDDEN_CHANGED, Boolean.FALSE, Boolean.TRUE);
		correspondingFeature.fireEvent(event);
	}

	protected void fireMandatoryChanged() {
		final PropertyChangeEvent event = new PropertyChangeEvent(this, MANDATORY_CHANGED, Boolean.FALSE, Boolean.TRUE);
		correspondingFeature.fireEvent(event);
	}

	@Override
	public int getChildIndex(IFeatureStructure feature) {
		return children.indexOf(feature);
	}

	@Override
	public List<IFeatureStructure> getChildren() {	// Changed type LinkedList to List, Marcus Pinnecke 30.08.15
		return children;
	}

	@Override
	public int getChildrenCount() {
		return children.size();
	}

	@Override
	public IFeature getFeature() {
		return correspondingFeature;
	}

	@Override
	public IFeatureStructure getFirstChild() {
		if (children.isEmpty()) {
			return null;
		}
		return children.get(0);
	}

	@Override
	public IFeatureStructure getLastChild() {
		if (!children.isEmpty()) {
			return children.getLast();
		}
		return null;
	}

	@Override
	public IFeatureStructure getParent() {
		return parent;
	}

	@Override
	public Collection<IConstraint> getRelevantConstraints() {
		return partOfConstraints;
	}

	@Override
	public List<FeatureConnection> getSourceConnections() {
		return parent == null ? Collections.<FeatureConnection> emptyList() : sourceConnections;
	}

	@Override
	public List<FeatureConnection> getTargetConnections() {
		return targetConnections;
	}

	@Override
	public boolean hasChildren() {
		return !children.isEmpty();
	}

	@Override
	public boolean hasHiddenParent() {

		if (isHidden()) {
			return true;
		}
		if (isRoot()) {

			return false;
		}
		IFeatureStructure p = getParent();

		while (!p.isRoot()) {
			if (p.isHidden()) {
				return true;
			}
			p = p.getParent();

		}

		return false;
	}

	/**
	 * Returns true if the rule can be writen in a format like 'Ab [Cd] Ef ::
	 * Gh'.
	 */
	@Override
	public boolean hasInlineRule() {
		return (getChildrenCount() > 1) && and && isMandatory() && !multiple;
	}

	@Override
	public boolean isAbstract() {
		return !isConcrete();
	}

	@Override
	public boolean isAlternative() {
		return !and && !multiple;
	}

	@Override
	public boolean isAncestorOf(IFeatureStructure next) {
		while (next.getParent() != null) {
			if (next.getParent() == getParent()) {
				return true;
			}
			next = next.getParent();
		}
		return false;
	}

	@Override
	public boolean isAnd() {
		return and;
	}

	@Override
	public boolean isANDPossible() {
		if ((parent == null) || parent.isAnd()) {
			return false;
		}
		for (final IFeatureStructure child : children) {
			if (child.isAnd()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean isConcrete() {
		return concrete;
	}

	@Override
	public boolean isFirstChild(IFeatureStructure child) {
		return children.indexOf(child) == 0;
	}

	@Override
	public boolean isHidden() {
		return hidden;
	}

	@Override
	public boolean isMandatory() {
		return (parent == null) || !parent.isAnd() || mandatory;
	}

	@Override
	public boolean isMandatorySet() {
		return mandatory;
	}

	@Override
	public boolean isMultiple() {
		return multiple;
	}

	@Override
	public boolean isOr() {
		return !and && multiple;
	}

	@Override
	public boolean isRoot() {
		return parent == null;
	}

	@Override
	public void removeChild(IFeatureStructure child) {
		if(!children.remove(child))
			throw new NoSuchElementException();
		child.setParent(null);
		fireChildrenChanged();
	}

	@Override
	public IFeatureStructure removeLastChild() {
		final IFeatureStructure child = children.removeLast();
		child.setParent(null);
		fireChildrenChanged();
		return child;
	}

	@Override
	public boolean removeTargetConnection(FeatureConnection connection) {
		return targetConnections.remove(connection);
	}

	@Override
	public void replaceChild(IFeatureStructure oldChild, IFeatureStructure newChild) {
		final int index = children.indexOf(oldChild);
		children.set(index, newChild);
		oldChild.setParent(null);
		newChild.setParent(this);
		fireChildrenChanged();
	}

	@Override
	public void setAbstract(boolean value) {
		concrete = !value;
		fireChildrenChanged();
	}

	@Override
	public void setAlternative() {
		and = false;
		multiple = false;
	}

	@Override
	public void setAnd() {
		and = true;
	}

	@Override
	public void setAND(boolean and) {
		this.and = and;
		fireChildrenChanged();
	}

	@Override
	public void setChildren(List<IFeatureStructure> children) {	// Changed type LinkedList to List, Marcus Pinnecke 30.08.15
		this.children.clear();
		for (final IFeatureStructure child : children) {
			addNewChild(child);
		}
		fireChildrenChanged();
	}

	@Override
	public void setHidden(boolean hid) {
		hidden = hid;
		fireHiddenChanged();
	}

	@Override
	public void setMandatory(boolean mandatory) {
		this.mandatory = mandatory;
		fireMandatoryChanged();
	}

	@Override
	public void setMultiple(boolean multiple) {
		this.multiple = multiple;
		fireChildrenChanged();
	}

	@Override
	public void setOr() {
		and = false;
		multiple = true;
	}

	@Override
	public void setParent(IFeatureStructure newParent) {
		if (newParent == parent) {
			return;
		}

		// delete old parent connection (if existing)
		if (parent != null) {
			parent.removeTargetConnection(parentConnection);
			parentConnection.setTarget(null);
		}

		// update the target
		parent = newParent;
		if (newParent != null) {
			parentConnection.setTarget(newParent.getFeature());
			newParent.addTargetConnection(parentConnection);
		}
	}

	@Override
	public void setRelevantConstraints() {
		final List<IConstraint> constraintList = new LinkedList<>();
		for (final IConstraint constraint : correspondingFeature.getFeatureModel().getConstraints()) {
			for (final IFeature f : constraint.getContainedFeatures()) {
				if (f.getName().equals(correspondingFeature.getName())) {
					constraintList.add(constraint);
					break;
				}
			}
		}
		partOfConstraints = constraintList;
	}

	@Override
	public void setRelevantConstraints(List<IConstraint> constraints) {
		partOfConstraints = constraints;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder("FeatureStructure=(");
		FeatureUtils.print(getFeature(), sb);
		sb.append(")");
		return sb.toString();
	}

}
