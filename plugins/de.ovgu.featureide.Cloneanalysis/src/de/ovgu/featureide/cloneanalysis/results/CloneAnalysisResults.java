package de.ovgu.featureide.cloneanalysis.results;

import java.util.HashSet;
import java.util.Set;

public class CloneAnalysisResults<T extends Clone> {
	private Set<T> clones;
	private IClonePercentageData percentageData;
	private Set<FeatureRootLocation> relevantFeatures;

	public CloneAnalysisResults(Set<T> clones) {
		this.clones = clones;
		relevantFeatures = new HashSet<FeatureRootLocation>();
	}

	// TODO: Feature awareness

	/**
	 * @return the number of clones
	 */
	public int getCloneCount() {
		return clones.size();
	}

	/**
	 * @return the clones
	 */
	public Set<T> getClones() {
		return clones;
	}

	/**
	 * @return the percentageData
	 */
	public IClonePercentageData getPercentageData() {
		return percentageData;
	}

	/**
	 * @param percentageData
	 *            the percentageData to set
	 */
	public void setPercentageData(IClonePercentageData percentageData) {
		this.percentageData = percentageData;
	}

	/**
	 * @return the relevantFeatures
	 */
	public Set<FeatureRootLocation> getRelevantFeatures() {
		return relevantFeatures;
	}

	/**
	 * @param relevantFeatures
	 *            the relevantFeatures to set
	 */
	public void setRelevantFeatures(Set<FeatureRootLocation> relevantFeatures) {
		this.relevantFeatures = relevantFeatures;
	}
}
