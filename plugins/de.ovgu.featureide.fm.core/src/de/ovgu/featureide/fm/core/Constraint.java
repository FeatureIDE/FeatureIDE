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
import java.util.AbstractCollection;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeWriter;

/**
 * Represents a propositional constraint below the feature diagram.
 * 
 * @author Thomas Thuem
 */
public class Constraint implements PropertyConstants {

	private FeatureModel featureModel;
	private Node propNode;
	private FMPoint location = new FMPoint(0,0);
	private boolean featureSelected = false;
	private List<Feature> containedFeatureList = new LinkedList<Feature>();
	private List<Feature> falseOptionalFeatures = new LinkedList<Feature>();
 	private ConstraintAttribute attribute = ConstraintAttribute.NORMAL;
	
	private List<Feature> deadFeatures = new ArrayList<Feature>();
	
	public Constraint(FeatureModel featureModel, Node propNode) {
		this.featureModel = featureModel;
		this.propNode = propNode;
	}
	
	public void setLocation(FMPoint newLocation){
		location = newLocation;
	}
	
	public FMPoint getLocation(){
		return location;
	}
	
	public FeatureModel getFeatureModel() {
		return featureModel;
	}
	
	/**
	 * Looks for all dead features if they ares caused dead by this constraint
	 * @param fm The model
	 * @param fmDeadFeatures The dead features of this model (This is calculated before, so the need to be generated only once)
	 * @return The dead features caused by this constraint
	 */
	public List<Feature> getDeadFeatures(FeatureModel fm, AbstractCollection<Feature> fmDeadFeatures) {
		List<Feature> deadFeaturesBefore = null;		
		Node propNode = this.getNode();
		if (propNode != null) {
			if (this != null) {
				fm.removePropositionalNode(this);
			}
			deadFeaturesBefore = fm.getAnalyser().getDeadFeatures();
			fm.addPropositionalNode(propNode);
			fm.handleModelDataChanged();
		}

		List<Feature> deadFeaturesAfter = new LinkedList<Feature>();
		for (Feature l : fmDeadFeatures) {
			if (!deadFeaturesBefore.contains(fm.getFeature(l.getName()))) {
				deadFeaturesAfter.add(l);
			}
		}
		return deadFeaturesAfter;
	}
	
	public void setConstraintAttribute(ConstraintAttribute attri, boolean fire){
		this.attribute = attri;
		if(fire)fire(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}
	
	public ConstraintAttribute getConstraintAttribute(){
		return attribute;
	}
	
	public void setFeatureSelected (boolean selected){
		this.featureSelected = selected;
		fire(new PropertyChangeEvent(this, CONSTRAINT_SELECTED, Boolean.FALSE, Boolean.TRUE));
	}
	
	public boolean isFeatureSelected(){
		return featureSelected;
	}
	
	public Node getNode() {
		return propNode;
	}	
	
	public void setContainedFeatures(Node actNode){
		if (actNode instanceof Literal) {
			containedFeatureList.add(featureModel.getFeature(((Literal) actNode).var.toString()));
		} else {
			for (Node child : actNode.getChildren()){
				setContainedFeatures(child);
			}
		}
	}

	public List<Feature> getContainedFeatures(){
		return containedFeatureList;
	}

	public boolean setFalseOptionalFeatures(){
		falseOptionalFeatures.clear();
		boolean found=false;
		FeatureModel clonedModel = featureModel.clone();
		clonedModel.removePropositionalNode(this);
		LinkedList<Feature> foFeatures = clonedModel.getAnalyser().getFalseOptionalFeatures();
		for (Feature feature : featureModel.getFalseOptionalFeatures()) {
			if (!foFeatures.contains(clonedModel.getFeature(feature.getName())) && !falseOptionalFeatures.contains(feature)) {
				falseOptionalFeatures.add(feature);
				found = true;
			}
		}
		return found;
	}
	
	public List<Feature> getFalseOptional(){
		return falseOptionalFeatures;
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
	
	@Override
	public String toString(){
		return propNode.toString(NodeWriter.textualSymbols);
	}

	/**
	 * Set the dead features of this constraint
	 * @param deadFeatures
	 */
	public void setDeadFeatures(List<Feature> deadFeatures) {
		this.deadFeatures  = deadFeatures; 
	}
	
	/**
	 * Gets the dead features of this constraint without new calculation
	 * @return The dead features
	 */
	public List<Feature> getDeadFeatures() {
		return deadFeatures;
	}

}
