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
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;

import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureComparator;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Represents a propositional constraint below the feature diagram.
 * 
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class Constraint implements IConstraint, PropertyConstants {

	private final Collection<PropertyChangeListener> listenerList = new LinkedList<>();

	private final IFeatureModel featureModel;
	private final Node propNode;

	private final Collection<IFeature> containedFeatureList = new LinkedList<>();
	private final Collection<IFeature> falseOptionalFeatures = new LinkedList<>();
	private final Collection<IFeature> deadFeatures = new LinkedList<>();

	private ConstraintAttribute attribute = ConstraintAttribute.NORMAL;

	public Constraint(IFeatureModel featureModel, Node propNode) {
		this.featureModel = featureModel;
		this.propNode = propNode;
	}

	/**
	 * Looks for all dead features if they ares caused dead by this constraint
	 * 
	 * @param solver
	 * @param fm The actual model
	 * @param fmDeadFeatures The dead features the complete model
	 * @return The dead features caused by this constraint
	 */
	@Override
	public Collection<IFeature> getDeadFeatures(SatSolver solver, IFeatureModel fm, Collection<IFeature> fmDeadFeatures) {
		final Collection<IFeature> deadFeatures;
		final Node propNode = this.getNode();
		final Comparator<IFeature> featComp = new FeatureComparator(true);
		if (propNode != null) {
			deadFeatures = fm.getAnalyser().getDeadFeatures(solver, propNode);
		} else {
			deadFeatures = new TreeSet<IFeature>(featComp);
		}
		final Collection<IFeature> deadFeaturesAfter = new TreeSet<>(featComp);

		deadFeaturesAfter.addAll(fmDeadFeatures);
		deadFeaturesAfter.retainAll(deadFeatures);
		return deadFeaturesAfter;
	}

	@Override
	public boolean setFalseOptionalFeatures(IFeatureModel clone, Collection<IFeature> fmFalseOptionals) {
		falseOptionalFeatures.clear();
		falseOptionalFeatures.addAll(clone.getAnalyser().getFalseOptionalFeatures(fmFalseOptionals));
		fmFalseOptionals.removeAll(falseOptionalFeatures);
		return !falseOptionalFeatures.isEmpty();
	}

	private void fire(PropertyChangeEvent event) {
		fireEvent(event);
	}

	@Override
	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener)) {
			listenerList.add(listener);
		}
	}

	@Override
	public ConstraintAttribute getConstraintAttribute() {
		return attribute;
	}

	/**
	 * Sets the <code>containedFeatureList</code> given by <code>propNode</code>.
	 */
	@Override
	public void setContainedFeatures() {
		containedFeatureList.clear();
		for (String featureName : propNode.getContainedFeatures()) {
			containedFeatureList.add(featureModel.getFeature(featureName));
		}
	}

	/**
	 * 
	 * @return All {@link Feature}s contained at this {@link Constraint}.
	 */
	@Override
	public Collection<IFeature> getContainedFeatures() {
		if (containedFeatureList.isEmpty()) {
			setContainedFeatures();
		}
		return containedFeatureList;
	}

	@Override
	public Collection<IFeature> getDeadFeatures() {
		return deadFeatures;
	}

	@Override
	public Collection<IFeature> getFalseOptional() {
		return falseOptionalFeatures;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	@Override
	public Node getNode() {
		return propNode;
	}

	@Override
	public boolean hasHiddenFeatures() {
		for (IFeature f : getContainedFeatures()) {
			if (f.getFeatureStructure().isHidden() || f.getFeatureStructure().hasHiddenParent()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}

	@Override
	public void setConstraintAttribute(ConstraintAttribute attri, boolean fire) {
		this.attribute = attri;
		if (fire) {
			fire(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, Boolean.FALSE, Boolean.TRUE));
		}

	}

	@Override
	public void setDeadFeatures(Collection<IFeature> deadFeatures) {
		this.deadFeatures.clear();
		this.deadFeatures.addAll(deadFeatures);
	}

	@Override
	public void fireEvent(PropertyChangeEvent event) {
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

}
