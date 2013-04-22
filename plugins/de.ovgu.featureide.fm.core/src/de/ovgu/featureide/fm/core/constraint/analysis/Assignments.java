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

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 */
public class Assignments {

	private Set<Feature> positiveAssignments;
	
	private Set<Feature> negativeAssignments;
	
	public Assignments() {
		positiveAssignments = new HashSet<Feature>();
		negativeAssignments = new HashSet<Feature>();
	}
	
	public void addPositiveAssignment(Feature feature) {
		positiveAssignments.add(feature);
	}
	
	public void addNegativeAssignment(Feature feature) {
		negativeAssignments.add(feature);
	}
	
	public Set<Feature> getPositiveAssignments() {
		return Collections.unmodifiableSet(positiveAssignments);
	}
	
	public Set<Feature> getNegativeAssignments() {
		return Collections.unmodifiableSet(negativeAssignments);
	}
	
	public Boolean getAssignment(Feature feature) {
		if (positiveAssignments.contains(feature)) {
			return true;
		} else if (negativeAssignments.contains(feature)) {
			return false;
		} else {
			return null;
		}
	}
	
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("enabled features:  ");
		
		for (Iterator<Feature> it = positiveAssignments.iterator(); it.hasNext();) {
			Feature feature = (Feature) it.next();
			sb.append(feature.getName());
			if (it.hasNext())
				sb.append(", ");
		}
		
		sb.append("\n");
		
		sb.append("disabled features: ");
		for (Iterator<Feature> it = negativeAssignments.iterator(); it.hasNext();) {
			Feature feature = (Feature) it.next();
			sb.append(feature.getName());
			if (it.hasNext())
				sb.append(", ");
		}
		
		return sb.toString();
	}
}
