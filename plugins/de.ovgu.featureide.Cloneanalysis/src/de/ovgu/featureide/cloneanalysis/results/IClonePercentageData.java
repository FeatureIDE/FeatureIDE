package de.ovgu.featureide.cloneanalysis.results;

public interface IClonePercentageData {

	public abstract double getClonedLinePercentage(FeatureRootLocation feature);

	public abstract long getTotalLineCount(FeatureRootLocation feature);

	public abstract long getTotalCloneLength(FeatureRootLocation feature);

	public abstract int getClonedLineCount(FeatureRootLocation feature);

}