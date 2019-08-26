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
	 * @param percentageData the percentageData to set
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
	 * @param relevantFeatures the relevantFeatures to set
	 */
	public void setRelevantFeatures(Set<FeatureRootLocation> relevantFeatures) {
		this.relevantFeatures = relevantFeatures;
	}
}
