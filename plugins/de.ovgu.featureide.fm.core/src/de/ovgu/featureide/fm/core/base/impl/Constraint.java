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
import de.ovgu.featureide.fm.core.FeatureComparator;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IGraphicalConstraint;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Represents a propositional constraint below the feature diagram.
 * 
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class Constraint implements IConstraint, PropertyConstants {
	
	private static long NEXT_ID = 0;
	
	protected static final synchronized long getNextId() {
		return NEXT_ID++;
	}

	private final long id;

	protected ConstraintAttribute attribute = ConstraintAttribute.NORMAL;

	protected final Collection<IFeature> containedFeatureList = new LinkedList<>();
	protected final Collection<IFeature> deadFeatures = new LinkedList<>();

	protected final Collection<IFeature> falseOptionalFeatures = new LinkedList<>();
	protected final IFeatureModel featureModel;
	protected final Collection<PropertyChangeListener> listenerList = new LinkedList<>();
	
	protected IGraphicalConstraint graphicalRepresentation;

	protected final Node propNode;
	boolean featureSelected;

	protected Constraint(Constraint oldConstraint, IFeatureModel featureModel) {
		this.featureModel = featureModel;
		this.id = oldConstraint.id;
		this.propNode = oldConstraint.propNode;
		this.featureSelected = oldConstraint.featureSelected;
		this.graphicalRepresentation = GraphicMap.getInstance().getGraphicRepresentation(this);
	}

	public Constraint(IFeatureModel featureModel, Node propNode) {
		this.featureModel = featureModel;
		this.id = getNextId();
		this.propNode = propNode;
		this.featureSelected = false;
		this.graphicalRepresentation = GraphicMap.getInstance().getGraphicRepresentation(this);
	}

	@Override
	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener)) {
			listenerList.add(listener);
		}
	}

	@Override
	public IConstraint clone(IFeatureModel newFeatureModel) {
		return new Constraint(this, newFeatureModel);
	}

	protected void fire(PropertyChangeEvent event) {
		fireEvent(event);
	}

	@Override
	public void fireEvent(PropertyChangeEvent event) {
		for (final PropertyChangeListener listener : listenerList) {
			listener.propertyChange(event);
		}
	}

	@Override
	public ConstraintAttribute getConstraintAttribute() {
		return attribute;
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
		final Node propNode = getNode();
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
	public String getDisplayName() {
		return propNode.toString();
	}

	@Override
	public boolean hasHiddenFeatures() {
		for (final IFeature f : getContainedFeatures()) {
			if (f.getStructure().isHidden() || f.getStructure().hasHiddenParent()) {
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
		attribute = attri;
		if (fire) {
			fire(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, Boolean.FALSE, Boolean.TRUE));
		}

	}

	/**
	 * Sets the <code>containedFeatureList</code> given by <code>propNode</code>.
	 */
	@Override
	public void setContainedFeatures() {
		containedFeatureList.clear();
		for (final String featureName : propNode.getContainedFeatures()) {
			containedFeatureList.add(featureModel.getFeature(featureName));
		}
	}

	@Override
	public void setDeadFeatures(Iterable<IFeature> deadFeatures) {
		this.deadFeatures.clear();
		this.deadFeatures.addAll(Functional.toList(deadFeatures));
	}

	@Override
	public boolean setFalseOptionalFeatures(IFeatureModel clone, Collection<IFeature> fmFalseOptionals) {
		falseOptionalFeatures.clear();
		falseOptionalFeatures.addAll(clone.getAnalyser().getFalseOptionalFeatures(fmFalseOptionals));
		fmFalseOptionals.removeAll(falseOptionalFeatures);
		return !falseOptionalFeatures.isEmpty();
	}

	@Override
	public IGraphicalConstraint getGraphicRepresenation() {
		return graphicalRepresentation;
	}

	@Override
	public boolean isFeatureSelected() {
		return featureSelected; 
	}

	@Override
	public void setFeatureSelected(boolean b) {
		featureSelected = b;
		fireEvent(new PropertyChangeEvent(this, CONSTRAINT_SELECTED, Boolean.FALSE, Boolean.TRUE));
	}
	

//	@Override
//	public int hashCode() { // Marcus: required for Constraints.remove(Constraint), e.g. Generator.java:124
////		final int prime = 31;
////		int result = 1;
////		result = prime * result + ((propNode == null) ? 0 : propNode.hashCode());
//		return ((propNode == null) ? 0 : propNode.hashCode());
//	}
//
//	@Override
//	public boolean equals(Object obj) {		// Marcus: required for Constraints.remove(Constraint), e.g. Generator.java:124
//		if (this == obj)
//			return true;
//		if (obj == null || getClass() != obj.getClass())
//			return false;
//		Constraint other = (Constraint) obj;
//		return (propNode != null && propNode.equals(other.propNode));
//	}
	
	@Override
	public int hashCode() {
		return (int) (37 * id);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		Constraint other = (Constraint) obj;
		return id == other.id;
	}

}
