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
package de.ovgu.featureide.deltaj;

import java.util.ArrayList;
import java.util.Collection;

import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author Sven Schuster
 */
public class DeltajSPLDefinition {
	private String name;
	private Collection<Feature> features; 
	private String deltas;
	
	public DeltajSPLDefinition() {
		this.features = new ArrayList<Feature>();
	}
	
	@Override
	public String toString() {
		String splFile = "spl " + this.getName() + " {\n";
		splFile += "features ";
		int i = 0;
		for(Feature f : features) {
			if(i++ != 0)
				splFile += ", ";
			splFile += f.getName();
		}
		splFile += "\n";
		splFile += "configurations true" + "\n"; // because featureide only allows valid configurations
		splFile += this.getDeltas();
		splFile += "}\n\n";
		return splFile;
	}
	
	public void setDeltas(String deltas) {
		this.deltas = deltas;
	}
	
	public String getDeltas() {
		return this.deltas;
	}
	
	public void setName(String name) {
		this.name = name;
	}
	
	public String getName() {
		return this.name;
	}
	
	public void addFeature(Feature feature) {
		this.features.add(feature);
	}
	
	public void addAllFeatures(Collection<Feature> features) {
		for(Feature f : features)
			this.features.add(f);
	}
	
	public void removeFeature(String feature) {
		this.features.remove(feature);
	}
	
	public Collection<Feature> getFeatures() {
		return this.features;
	}
}