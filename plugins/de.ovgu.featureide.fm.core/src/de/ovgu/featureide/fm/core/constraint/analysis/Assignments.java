package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.ovgu.featureide.fm.core.Feature;

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
