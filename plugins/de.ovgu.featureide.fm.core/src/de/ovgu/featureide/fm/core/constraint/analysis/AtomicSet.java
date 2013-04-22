/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.HashSet;
import java.util.Set;

import de.ovgu.featureide.fm.core.Feature;

/**
 * This class represents an atomic set which is a compound type of different
 * strongly connected features. 
 * 
 * @author Sebastian Henneberg
 */
public class AtomicSet {

	/**
	 * The identification number of this atomic set.
	 */
	private int id;
	
	/**
	 * The set of features owned by this atomic set.
	 */
	Set<Feature> features;
	
	/**
	 * Creates an empty atomic set.
	 * 
	 * @param id The id of this atomic set.
	 */
	public AtomicSet(int id) {
		this.id = id;
		this.features = new HashSet<Feature>();
	}
	
	/**
	 * Creates a new atomic set with an initial set of owned features.
	 * 
	 * @param id The id of this atomic set.
	 * @param features The set of features owned by this atomic set.
	 */
	public AtomicSet(int id, Set<Feature> features) {
		this.id = id;
		this.features = features;
	}
	
	/**
	 * Returns the id of this atomic set.
	 * 
	 * @return The id of this atomic set.
	 */
	public int getId() {
		return id;
	}
	
	/**
	 * Adds the specified feature to this atomic set.
	 * 
	 * @param feature The feature to add.
	 */
	public void	add(Feature feature) {
		features.add(feature);
	}
	
	/**
	 * Obtains the set of owned features.
	 * 
	 * @return The set of owned features.
	 */
	public Set<Feature> getFeatures() {
		return features;
	}
	
	/**
	 * Obtains the number of owned features.
	 * 
	 * @return The number of owned features.
	 */
	public int size() {
		return features.size();
	}
	
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("AtomicSet[");
		sb.append(id);
		sb.append("]:");
		
		for (Feature feature : features) {
			sb.append(" ");
			sb.append(feature.getName());
		}
		
		return sb.toString();
	}
}
