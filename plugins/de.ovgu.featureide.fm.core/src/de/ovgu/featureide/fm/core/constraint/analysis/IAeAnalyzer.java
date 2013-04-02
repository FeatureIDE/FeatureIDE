package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.List;

import de.ovgu.featureide.fm.core.Feature;

public interface IAeAnalyzer {

	public Assignments propagate(List<Feature> enabledFeatures, 
			List<Feature> disabledFeatures) throws ContradictionException;
	
	public Assignments getOptimalProduct();
}
