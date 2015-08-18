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

import de.ovgu.featureide.fm.core.FeatureConnection;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Provides all properties of a feature. This includes its connections to parent
 * and child features.
 * 
 * @author Thomas Thuem
 * @author Sebastian Krieter
 * 
 */
public class FeatureStructure implements IFeatureStructure, PropertyConstants {

	private static final List<FeatureConnection> EMPTY_LIST = Collections.<FeatureConnection> emptyList();

	private final IFeature correspondingFeature;

	private final LinkedList<FeatureConnection> sourceConnections = new LinkedList<FeatureConnection>();
	private final LinkedList<FeatureConnection> targetConnections = new LinkedList<FeatureConnection>();
	private FeatureConnection parentConnection;

	private List<IConstraint> partOfConstraints = new LinkedList<>();

	private LinkedList<IFeature> children = new LinkedList<>();
	private IFeature parent = null;

	private boolean and;
	private boolean concrete;
	private boolean hidden;
	private boolean mandatory;
	private boolean multiple;

	protected FeatureStructure(IFeatureStructure featureStructure, IFeature feature) {
		this.correspondingFeature = feature;

		this.mandatory = featureStructure.isMandatory();
		this.concrete = featureStructure.isConcrete();
		this.and = featureStructure.isAnd();
		this.multiple = featureStructure.isMultiple();
		this.hidden = featureStructure.isHidden();
		this.parentConnection = new FeatureConnection(this.correspondingFeature);

		this.children = new LinkedList<>();
		for (IFeature child : featureStructure.getChildren()) {
			this.children.add(feature.getFeatureModel().getFeature(child.getName()));
		}
		if (featureStructure.getParent() != null) {
			this.parent = feature.getFeatureModel().getFeature(featureStructure.getParent().getName());
		}
	}

	public FeatureStructure(IFeature correspondingFeature) {
		this.correspondingFeature = correspondingFeature;

		this.mandatory = false;
		this.concrete = true;
		this.and = true;
		this.multiple = false;
		this.hidden = false;
		this.parent = null;
		this.parentConnection = new FeatureConnection(this.correspondingFeature);
		sourceConnections.add(parentConnection);
	}

	public void addChild(IFeature newChild) {
		children.add(newChild);
		newChild.getFeatureStructure().setParent(this.getFeature());
		fireChildrenChanged();
	}

	public void addChildAtPosition(int index, IFeature newChild) {
		children.add(index, newChild);
		newChild.getFeatureStructure().setParent(this.getFeature());
		fireChildrenChanged();
	}

	public void addTargetConnection(FeatureConnection connection) {
		targetConnections.add(connection);
	}

	public void changeToAlternative() {
		and = false;
		multiple = false;
		fireChildrenChanged();
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

	private void fireChildrenChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this, CHILDREN_CHANGED, Boolean.FALSE, Boolean.TRUE);
		correspondingFeature.fireEvent(event);
	}

	private void fireHiddenChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this, HIDDEN_CHANGED, Boolean.FALSE, Boolean.TRUE);
		correspondingFeature.fireEvent(event);
	}

	private void fireMandatoryChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this, MANDATORY_CHANGED, Boolean.FALSE, Boolean.TRUE);
		correspondingFeature.fireEvent(event);
	}

	public int getChildIndex(IFeature feature) {
		return children.indexOf(feature);
	}

	public LinkedList<IFeature> getChildren() {
		return children;
	}

	public int getChildrenCount() {
		return children.size();
	}

	@Override
	public IFeature getFeature() {
		return correspondingFeature;
	}

	public IFeature getFirstChild() {
		if (children.isEmpty())
			return null;
		return children.get(0);
	}

	public IFeature getLastChild() {
		if (!children.isEmpty()) {
			return children.getLast();
		}
		return null;
	}

	public IFeature getParent() {
		return parent;
	}

	public Collection<IConstraint> getRelevantConstraints() {
		return partOfConstraints;
	}

	public List<FeatureConnection> getSourceConnections() {
		return parent == null ? EMPTY_LIST : sourceConnections;
	}

	public List<FeatureConnection> getTargetConnections() {
		return targetConnections;
	}

	public boolean hasChildren() {
		return !children.isEmpty();
	}

	public boolean hasHiddenParent() {

		if (isHidden())
			return true;
		if (isRoot()) {

			return false;
		}
		IFeature p = getParent();

		while (!p.getFeatureStructure().isRoot()) {
			if (p.getFeatureStructure().isHidden())
				return true;
			p = p.getFeatureStructure().getParent();

		}

		return false;
	}

	/**
	 * Returns true if the rule can be writen in a format like 'Ab [Cd] Ef ::
	 * Gh'.
	 */
	public boolean hasInlineRule() {
		return getChildrenCount() > 1 && and && isMandatory() && !multiple;
	}

	public boolean isAbstract() {
		return !isConcrete();
	}

	public boolean isAlternative() {
		return !and && !multiple;
	}

	public boolean isAncestorOf(IFeature next) {
		while (next.getFeatureStructure().getParent() != null) {
			if (next.getFeatureStructure().getParent() == this.getParent())
				return true;
			next = next.getFeatureStructure().getParent();
		}
		return false;
	}

	public boolean isAnd() {
		return and;
	}

	public boolean isANDPossible() {
		if (parent == null || parent.getFeatureStructure().isAnd())
			return false;
		for (IFeature child : children) {
			if (child.getFeatureStructure().isAnd())
				return false;
		}
		return true;
	}

	public boolean isConcrete() {
		return concrete;
	}

	public boolean isFirstChild(IFeature child) {
		return children.indexOf(child) == 0;
	}

	public boolean isHidden() {
		return hidden;
	}

	public boolean isMandatory() {
		return parent == null || !parent.getFeatureStructure().isAnd() || mandatory;
	}

	public boolean isMandatorySet() {
		return mandatory;
	}

	public boolean isMultiple() {
		return multiple;
	}

	public boolean isOr() {
		return !and && multiple;
	}

	public boolean isRoot() {
		return parent == null;
	}

	public void removeChild(IFeature child) {
		children.remove(child);
		child.getFeatureStructure().setParent(null);
		fireChildrenChanged();
	}

	public IFeature removeLastChild() {
		IFeature child = children.removeLast();
		child.getFeatureStructure().setParent(null);
		fireChildrenChanged();
		return child;
	}

	public boolean removeTargetConnection(FeatureConnection connection) {
		return targetConnections.remove(connection);
	}

	public void replaceChild(IFeature oldChild, IFeature newChild) {
		int index = children.indexOf(oldChild);
		children.set(index, newChild);
		oldChild.getFeatureStructure().setParent(null);
		newChild.getFeatureStructure().setParent(this.getFeature());
		fireChildrenChanged();
	}

	public void setAbstract(boolean value) {
		this.concrete = !value;
		fireChildrenChanged();
	}

	public void setAlternative() {
		this.and = false;
		this.multiple = false;
	}

	public void setAnd() {
		this.and = true;
	}

	public void setAND(boolean and) {
		this.and = and;
		fireChildrenChanged();
	}

	public void setChildren(LinkedList<IFeature> children) {
		if (this.children == children)
			return;
		for (IFeature child : children) {
			child.getFeatureStructure().setParent(this.getFeature());
		}
		this.children = children;
		fireChildrenChanged();
	}

	public void setHidden(boolean hid) {
		this.hidden = hid;
		fireHiddenChanged();
	}

	public void setMandatory(boolean mandatory) {
		this.mandatory = mandatory;
		fireMandatoryChanged();
	}

	public void setMultiple(boolean multiple) {
		this.multiple = multiple;
		fireChildrenChanged();
	}

	public void setOr() {
		this.and = false;
		this.multiple = true;
	}

	public void setParent(IFeature newParent) {
		if (newParent == parent)
			return;

		// delete old parent connection (if existing)
		if (parent != null) {
			parent.getFeatureStructure().removeTargetConnection(parentConnection);
			parentConnection.setTarget(null);
		}

		// update the target
		parent = newParent;
		if (newParent != null) {
			parentConnection.setTarget(newParent);
			newParent.getFeatureStructure().addTargetConnection(parentConnection);
		}
	}

	public void setRelevantConstraints() {
		List<IConstraint> constraintList = new LinkedList<>();
		for (IConstraint constraint : correspondingFeature.getFeatureModel().getConstraints()) {
			for (IFeature f : constraint.getContainedFeatures()) {
				if (f.getName().equals(correspondingFeature.getName())) {
					constraintList.add(constraint);
					break;
				}
			}
		}
		partOfConstraints = constraintList;
	}

}
