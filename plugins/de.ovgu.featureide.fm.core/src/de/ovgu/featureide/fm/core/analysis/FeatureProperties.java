/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.explanations.Explanation;

/**
 * All additional properties of an {@link IFeature}.
 *
 * @author Sebastian Krieter
 */
public class FeatureProperties {

	public static enum FeatureSelectionStatus {
		UNKNOWN, COMMON, DEAD, CORE
	}

	public static enum FeatureDeterminedStatus {
		UNKNOWN, INDETERMINATE, DETERMINATE, INDETERMINATE_HIDDEN
	}

	public static enum FeatureParentStatus {
		UNKNOWN, OPTIONAL, MANDATORY, GROUP, FALSE_OPTIONAL
	}

	protected final IFeature feature;

	private FeatureSelectionStatus featureSelectionStatus = FeatureSelectionStatus.UNKNOWN;
	private FeatureDeterminedStatus featureDeterminedStatus = FeatureDeterminedStatus.UNKNOWN;
	private FeatureParentStatus featureParentStatus = FeatureParentStatus.UNKNOWN;

	/**
	 * Explanation for dead features.
	 */
	private Explanation deadExplanation;

	/**
	 * Explanation for false-optional features.
	 */
	private Explanation falseOptionalExplanation;

	public FeatureProperties(IFeature feature) {
		this.feature = feature;
	}

	public IFeature getFeature() {
		return feature;
	}

	public boolean hasStatus(FeatureSelectionStatus featureSelectionStatus) {
		return this.featureSelectionStatus == featureSelectionStatus;
	}

	public boolean hasStatus(FeatureDeterminedStatus featureDeterminedStatus) {
		return this.featureDeterminedStatus == featureDeterminedStatus;
	}

	public boolean hasStatus(FeatureParentStatus featureParentStatus) {
		return this.featureParentStatus == featureParentStatus;
	}

	public Explanation getFalseOptionalExplanation() {
		return falseOptionalExplanation;
	}

	public void setFalseOptionalExplanation(Explanation falseOptionalExplanation) {
		this.falseOptionalExplanation = falseOptionalExplanation;
	}

	public Explanation getDeadExplanation() {
		return deadExplanation;
	}

	public void setDeadExplanation(Explanation deadExplanation) {
		this.deadExplanation = deadExplanation;
	}

	public FeatureSelectionStatus getFeatureSelectionStatus() {
		return featureSelectionStatus;
	}

	public void setFeatureSelectionStatus(FeatureSelectionStatus featureSelectionStatus) {
		this.featureSelectionStatus = featureSelectionStatus;
	}

	public FeatureDeterminedStatus getFeatureDeterminedStatus() {
		return featureDeterminedStatus;
	}

	public void setFeatureDeterminedStatus(FeatureDeterminedStatus featureDeterminedStatus) {
		this.featureDeterminedStatus = featureDeterminedStatus;
	}

	public FeatureParentStatus getFeatureParentStatus() {
		return featureParentStatus;
	}

	public void setFeatureParentStatus(FeatureParentStatus featureParentStatus) {
		this.featureParentStatus = featureParentStatus;
	}

	public void resetStatus() {
		featureSelectionStatus = FeatureSelectionStatus.UNKNOWN;
		featureDeterminedStatus = FeatureDeterminedStatus.UNKNOWN;
		featureParentStatus = FeatureParentStatus.UNKNOWN;
	}

}
