/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

/**
 * TODO description
 * 
 * @author "Werner Jan"
 */
public class AnAttribute {

	protected String name;
	protected String value;
	protected String unit;
	protected boolean recursive;
	protected boolean configurable;
	protected String type;
	
//	protected AnAttribute(AnAttribute oldAttribute, IFeatureModel featureModel) {
//		super(oldAttribute, featureModel);
//		this.attNode = oldAttribute.attNode;
//	}

	public  AnAttribute() {
		recursive = false;
		configurable = false;
	}
	
	public void setName(String name) {
		this.name = name;
	}
	
	public void setUnit(String unit) {
		this.unit = unit;
	}
	

	public void setRecursive(boolean recursive) {
		this.recursive = recursive;
		// TODO Auto-generated method stub
		
	}

	public void setValue(String value) {
		this.value = value;
	}
	
	public void setType(String type) {
		this.type = type;
	}

	public void setConfigurable(boolean configurable) {
		this.configurable = configurable;
		
	}

	public String getName() {
		return name;	
	}
	
	public boolean getRecursive() {
		return recursive;	
	}

}


//@Override
//public Node getNode() {
//	return attNode;
//}
//
//public void setNode(Node node) {
//	this.attNode = node;
//}
//
//@Override
//public String getDisplayName() {
//	return attNode.toString();
//}

///**
// * Sets the <code>containedFeatureList</code> given by <code>propNode</code>.
// */
//@Override
//public void setContainedFeatures() {
//	synchronized (containedFeatureList) {
//		containedFeatureList.clear();
//		for (final String featureName : attNode.getContainedFeatures()) {
//			containedFeatureList.add(featureModel.getFeature(featureName));
//		}
//	}
//}
//
//@Override
//public Collection<IFeature> getContainedFeatures() {
//	synchronized (containedFeatureList) {
//		if (containedFeatureList.isEmpty()) {
//			setContainedFeatures();
//		}
//		return containedFeatureList;
//	}
//}
//
///* (non-Javadoc)
// * @see de.ovgu.featureide.fm.core.base.IAttribute#clone(de.ovgu.featureide.fm.core.base.IFeatureModel)
// */
//@Override
//public IAttribute clone(IFeatureModel newFeatureModel) {
//	// TODO Auto-generated method stub
//	return null;
//}