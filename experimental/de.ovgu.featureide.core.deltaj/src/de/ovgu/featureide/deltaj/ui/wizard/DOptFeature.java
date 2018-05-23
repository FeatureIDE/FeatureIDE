/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.deltaj.ui.wizard;

import java.util.ArrayList;

/**
 * @author Andr� Specht
 * Adapted for FeatureIDE by Sven Schuster
 */
public class DOptFeature {
	
	private ArrayList<String> features;
	private String deltaModule;
	
	public DOptFeature(String deltamod, ArrayList<String> features){
		this.features=features;
		this.deltaModule = deltamod;
	}
	
	public ArrayList<String> getFeatures() {
		return features;
	}
	public void setFeature(ArrayList<String> feature) {
		this.features = feature;
	}
	public String getDeltaModule() {
		return deltaModule;
	}
	public void setDeltaModule(String deltaModule) {
		this.deltaModule = deltaModule;
	}
	
	public String getProp(){
		String prop ="";
		if(this.features.isEmpty())
			return null;
		else{
			
			for (String f : this.features) {
				if(!(f.equals(features.get(features.size()-1))))
					prop +=f+" && ";
				else
					prop +=f;
			}
			return prop;
		}
	}

}
