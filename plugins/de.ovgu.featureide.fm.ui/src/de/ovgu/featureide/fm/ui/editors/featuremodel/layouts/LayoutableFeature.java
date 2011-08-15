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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.Collection;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.Feature;

/**
 * 
 * @author Patrick Sulkowski
 */
public class LayoutableFeature {
	
	private static boolean showHidden;
	private Feature feature;
	
	
	public LayoutableFeature(Feature feature, boolean showHidden) {
		this.feature = feature;
		this.showHidden = showHidden;
	}
	
	public LinkedList<LayoutableFeature> getChildren() {
		
		LinkedList<LayoutableFeature> children = new LinkedList<LayoutableFeature>();
		
		for(Feature child : feature.getChildren()){
			if(showHidden) {
				children.add(new LayoutableFeature(child, showHidden));
			} else {
				if(!child.isHidden()) {
					children.add(new LayoutableFeature(child, showHidden));
				}
			}
			
				
		}
		return children;
		
	}
	public LayoutableFeature getFirstChild() {
		if (getChildren().isEmpty())
			return null;		
		return getChildren().get(0);
	}

	public LayoutableFeature getLastChild() {
		if (!getChildren().isEmpty()) {
			return getChildren().getLast();
		}
		return null;
	}
	
	public boolean hasChildren() {
		return !getChildren().isEmpty();
	}
	
	public Feature getFeature(){
		return feature;
	}
	
	public static LinkedList<Feature> createLayoutableFeatures(
			Collection<Feature> features, boolean showHidden){
		
		LinkedList<Feature> newFeatures = new LinkedList<Feature>();
		
		for(Feature feature : features){
			if(showHidden) {
				newFeatures.add(feature);
			} else {
				if(!isHidden(feature)){
					newFeatures.add(feature);
				}
			}
				
		}
		return newFeatures;
	}

	static boolean isHidden(Feature feature){
		if(showHidden){
			return false;
		} else {
			if(feature.isHidden()){
				return feature.isHidden();
			}
			if(!feature.isRoot()){
				return isHidden(feature.getParent());
			} else {
				return feature.isHidden();
			}
		}

	}
	
}
