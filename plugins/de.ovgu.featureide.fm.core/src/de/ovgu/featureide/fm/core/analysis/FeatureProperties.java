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
package de.ovgu.featureide.fm.core.analysis;

import java.util.EnumSet;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.explanations.Explanation;

/**
 * All additional properties of an {@link IFeature}.
 *
 * @author Sebastian Krieter
 */
public class FeatureProperties {

	public static enum FeatureStatus {
		COMMON, DEAD, CORE, INDETERMINATE, DETERMINATE, INDETERMINATE_HIDDEN, OPTIONAL, MANDATORY, GROUP, FALSE_OPTIONAL
	}

	private static final EnumSet<FeatureStatus> featureSelectionStatus = EnumSet.of(FeatureStatus.COMMON, FeatureStatus.DEAD, FeatureStatus.CORE);
	private static final EnumSet<FeatureStatus> featureDeterminedStatus =
		EnumSet.of(FeatureStatus.INDETERMINATE, FeatureStatus.DETERMINATE, FeatureStatus.INDETERMINATE_HIDDEN);
	private static final EnumSet<FeatureStatus> featureParentStatus =
		EnumSet.of(FeatureStatus.OPTIONAL, FeatureStatus.MANDATORY, FeatureStatus.GROUP, FeatureStatus.FALSE_OPTIONAL);

	private final EnumSet<FeatureStatus> featureStatus = EnumSet.noneOf(FeatureStatus.class);

	protected final IFeature feature;

	/**
	 * Explanation for dead features.
	 */
	private Explanation<?> deadExplanation;

	/**
	 * Explanation for false-optional features.
	 */
	private Explanation<?> falseOptionalExplanation;

	public FeatureProperties(IFeature feature) {
		this.feature = feature;
	}

	public IFeature getFeature() {
		return feature;
	}

	public boolean hasStatus(FeatureStatus featureStatus) {
		return this.featureStatus.contains(featureStatus);
	}

	public void resetSelectionStatus() {
		featureStatus.removeAll(featureSelectionStatus);
	}

	public void resetParentStatus() {
		featureStatus.removeAll(featureParentStatus);
	}

	public void resetDeterminationStatus() {
		featureStatus.removeAll(featureDeterminedStatus);
	}

	public void resetStatus() {
		featureStatus.clear();
	}

	public void setStatus(FeatureStatus featureStatus) {
		if (featureSelectionStatus.contains(featureStatus)) {
			resetSelectionStatus();
		} else if (featureParentStatus.contains(featureStatus)) {
			resetParentStatus();
		} else if (featureDeterminedStatus.contains(featureStatus)) {
			resetDeterminationStatus();
		}
		this.featureStatus.add(featureStatus);
	}

	public Explanation<?> getFalseOptionalExplanation() {
		return falseOptionalExplanation;
	}

	public void setFalseOptionalExplanation(Explanation<?> falseOptionalExplanation) {
		this.falseOptionalExplanation = falseOptionalExplanation;
	}

	public Explanation<?> getDeadExplanation() {
		return deadExplanation;
	}

	public void setDeadExplanation(Explanation<?> deadExplanation) {
		this.deadExplanation = deadExplanation;
	}

	@Override
	public String toString() {
		return "FeatureProperties for " + feature.getName() + " " + featureStatus.toString();
	}

}
