package de.ovgu.featureide.cloneanalysis.results;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;

public class ClonePercentageData implements IClonePercentageData {
	private Map<FeatureRootLocation, Long> featureTotalLineCounts;
	private Map<FeatureRootLocation, Long> featureTotalCloneLength;
	private Map<FeatureRootLocation, Map<IFile, short[]>> featureClonedLinesPerFile;
	private Map<FeatureRootLocation, Integer> clonedLineCount;

	public ClonePercentageData() {
		featureTotalLineCounts = new HashMap<FeatureRootLocation, Long>();
		featureTotalCloneLength = new HashMap<FeatureRootLocation, Long>();
		featureClonedLinesPerFile = new HashMap<FeatureRootLocation, Map<IFile, short[]>>();
		clonedLineCount = new HashMap<FeatureRootLocation, Integer>();
	}

	public void setFeatureTotalLineCount(FeatureRootLocation feature, long lineCount) {
		if (featureTotalLineCounts.containsKey(feature))
			featureTotalLineCounts.remove(feature);
		featureTotalLineCounts.put(feature, new Long(lineCount));
	}

	public void setFeatureTotalCloneLength(FeatureRootLocation feature, long lineCount) {
		if (featureTotalCloneLength.containsKey(feature))
			featureTotalCloneLength.remove(feature);
		featureTotalCloneLength.put(feature, new Long(lineCount));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.cloneanalysis.results.IClonePercentageData#
	 * getClonedLinePercentage
	 * (de.ovgu.featureide.cloneanalysis.results.IFeature)
	 */
	@Override
	public double getClonedLinePercentage(FeatureRootLocation feature) {
		assert featureTotalLineCounts.get(feature) > featureTotalCloneLength
				.get(feature) : "There should not be more cloned than total lines";
		return featureTotalLineCounts.get(feature) / featureTotalCloneLength.get(feature);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.cloneanalysis.results.IClonePercentageData#
	 * getTotalLineCount(de.ovgu.featureide.cloneanalysis.results.IFeature)
	 */
	@Override
	public long getTotalLineCount(FeatureRootLocation feature) {
		return featureTotalLineCounts.get(feature);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.cloneanalysis.results.IClonePercentageData#
	 * getClonedLineCount(de.ovgu.featureide.cloneanalysis.results.IFeature)
	 */
	@Override
	public long getTotalCloneLength(FeatureRootLocation feature) {
		return featureTotalCloneLength.get(feature);
	}

	/**
	 * @return the featureClonedLines
	 */
	public Map<FeatureRootLocation, Map<IFile, short[]>> getFeatureClonedLinesPerFile() {
		return featureClonedLinesPerFile;
	}

	/**
	 * @param featureClonedLines
	 *            the featureClonedLines to set
	 */
	public void setFeatureClonedLinesPerFile(FeatureRootLocation feature, Map<IFile, short[]> featureClonedLines) {
		if (featureClonedLinesPerFile.containsKey(feature))
			featureClonedLinesPerFile.remove(feature);
		featureClonedLinesPerFile.put(feature, featureClonedLines);
	}

	@Override
	public int getClonedLineCount(FeatureRootLocation feature) {
		return calculateClonedLineCount(feature);
	}

	/**
	 * @return the lineCount
	 */
	public int calculateClonedLineCount(FeatureRootLocation feature) {
		if (!clonedLineCount.containsKey(feature)) {
			int count = 0;
			for (short[] lines : featureClonedLinesPerFile.get(feature).values()) {
				for (short cloneCount : lines)
					if (cloneCount > 0)
						count++;
			}
			clonedLineCount.put(feature, new Integer(count));
		}
		final Integer result = clonedLineCount.get(feature);
		return result == null ? -1 : result;
	}

	public void setFeatureClonedLinesPerFile(Map<FeatureRootLocation, Map<IFile, short[]>> featureClonedLinesPerFile2) {
		this.featureClonedLinesPerFile = featureClonedLinesPerFile2;
	}
}
