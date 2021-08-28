/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
		if (featureTotalLineCounts.containsKey(feature)) featureTotalLineCounts.remove(feature);
		featureTotalLineCounts.put(feature, Long.valueOf(lineCount));
	}

	public void setFeatureTotalCloneLength(FeatureRootLocation feature, long lineCount) {
		if (featureTotalCloneLength.containsKey(feature)) featureTotalCloneLength.remove(feature);
		featureTotalCloneLength.put(feature, Long.valueOf(lineCount));
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.cloneanalysis.results.IClonePercentageData# getClonedLinePercentage (de.ovgu.featureide.cloneanalysis.results.IFeature)
	 */
	@Override
	public double getClonedLinePercentage(FeatureRootLocation feature) {
		assert featureTotalLineCounts.get(feature) > featureTotalCloneLength.get(feature) : "There should not be more cloned than total lines";
		return featureTotalLineCounts.get(feature) / featureTotalCloneLength.get(feature);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.cloneanalysis.results.IClonePercentageData# getTotalLineCount(de.ovgu.featureide.cloneanalysis.results.IFeature)
	 */
	@Override
	public long getTotalLineCount(FeatureRootLocation feature) {
		return featureTotalLineCounts.get(feature);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.cloneanalysis.results.IClonePercentageData# getClonedLineCount(de.ovgu.featureide.cloneanalysis.results.IFeature)
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
	 * 
	 * @param feature the features
	 * @param featureClonedLines the featureClonedLines to set
	 */
	public void setFeatureClonedLinesPerFile(FeatureRootLocation feature, Map<IFile, short[]> featureClonedLines) {
		if (featureClonedLinesPerFile.containsKey(feature)) featureClonedLinesPerFile.remove(feature);
		featureClonedLinesPerFile.put(feature, featureClonedLines);
	}

	@Override
	public int getClonedLineCount(FeatureRootLocation feature) {
		return calculateClonedLineCount(feature);
	}

	/**
	 * 
	 * @param feature feature root location
	 * @return the lineCount
	 */
	public int calculateClonedLineCount(FeatureRootLocation feature) {
		if (!clonedLineCount.containsKey(feature)) {
			int count = 0;
			for (short[] lines : featureClonedLinesPerFile.get(feature).values()) {
				for (short cloneCount : lines)
					if (cloneCount > 0) count++;
			}
			clonedLineCount.put(feature, Integer.valueOf(count));
		}
		final Integer result = clonedLineCount.get(feature);
		return result == null ? -1 : result;
	}

	public void setFeatureClonedLinesPerFile(Map<FeatureRootLocation, Map<IFile, short[]>> featureClonedLinesPerFile2) {
		this.featureClonedLinesPerFile = featureClonedLinesPerFile2;
	}
}
