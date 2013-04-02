package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Set;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.editing.Comparison;

public interface IDeAnalyzer {

	boolean isValid();
	
	Set<Feature> getDeadFeatures();
	
	Set<Feature> getFalseOptionalFeatures();
	
	Set<Feature> getCoreFeatures();
	
	Set<Feature> getVariantFeatures();
	
	AtomicSets getAtomicSets();
	
	Comparison getEditType(ExtendedFeatureModel efm);
}
