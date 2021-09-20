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

import java.util.Collection;
import java.util.HashMap;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * All additional properties of an {@link IFeature}.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class FeatureModelProperties {

	public enum FeatureModelStatus {
		VALID, ANOMALIES, VOID
	}

	private FeatureModelStatus featureModelStatus = FeatureModelStatus.VALID;

	private final Collection<FeatureProperties> featureProperties;
	private final Collection<ConstraintProperties> constraintProperties;

	public FeatureModelProperties(Collection<FeatureProperties> featureProperties, Collection<ConstraintProperties> constraintProperties) {
		this.featureProperties = featureProperties;
		this.constraintProperties = constraintProperties;
	}

	private final HashMap<FeatureStatus, Boolean> cachedFeatureStatus = new HashMap<>();
	private final HashMap<ConstraintStatus, Boolean> cachedConstraintStatus = new HashMap<>();

	public void setStatus(FeatureModelStatus featureModelStatus) {
		this.featureModelStatus = featureModelStatus;
	}

	public boolean hasStatus(FeatureModelStatus status) {
		return featureModelStatus == status;
	}

	public boolean hasStatus(FeatureStatus status) {
		Boolean cachedResult = cachedFeatureStatus.get(status);
		if (cachedResult == null) {
			cachedResult = testFor(status);
			cachedFeatureStatus.put(status, cachedResult);
		}
		return cachedResult;
	}

	public boolean hasStatus(ConstraintStatus status) {
		Boolean cachedResult = cachedConstraintStatus.get(status);
		if (cachedResult == null) {
			cachedResult = testFor(status);
			cachedConstraintStatus.put(status, cachedResult);
		}
		return cachedResult;
	}

	private boolean testFor(FeatureStatus status) {
		return featureProperties.stream().anyMatch(prop -> prop.hasStatus(status));
	}

	private boolean testFor(ConstraintStatus status) {
		return constraintProperties.stream().anyMatch(prop -> prop.hasStatus(status));
	}

	private Boolean hasFalseOptionalFeatures;

	public boolean hasFalseOptionalFeatures() {
		if (hasFalseOptionalFeatures == null) {
			hasFalseOptionalFeatures = testFor(FeatureStatus.FALSE_OPTIONAL);
		}
		return hasFalseOptionalFeatures;
	}

	private Boolean hasDeadFeatures;

	public boolean hasDeadFeatures() {
		if (hasDeadFeatures == null) {
			hasDeadFeatures = testFor(FeatureStatus.DEAD);
		}
		return hasDeadFeatures;
	}

	private Boolean hasIndeterminateHiddenFeatures;

	public boolean hasIndeterminateHiddenFeatures() {
		if (hasIndeterminateHiddenFeatures == null) {
			hasIndeterminateHiddenFeatures = testFor(FeatureStatus.INDETERMINATE_HIDDEN);
		}
		return hasIndeterminateHiddenFeatures;
	}

	private Boolean hasUnsatisfiableConstraints;

	public boolean hasUnsatisfiableConstraints() {
		if (hasUnsatisfiableConstraints == null) {
			hasUnsatisfiableConstraints = testFor(ConstraintStatus.UNSATISFIABLE);
		}
		return hasUnsatisfiableConstraints;
	}

	private Boolean hasTautologyConstraints;

	public boolean hasTautologyConstraints() {
		if (hasTautologyConstraints == null) {
			hasTautologyConstraints = testFor(ConstraintStatus.TAUTOLOGY);
		}
		return hasTautologyConstraints;
	}

	private Boolean hasDeadConstraints;

	public boolean hasDeadConstraints() {
		if (hasDeadConstraints == null) {
			hasDeadConstraints = constraintProperties.stream().anyMatch(prop -> !prop.getDeadFeatures().isEmpty());
		}
		return hasDeadConstraints;
	}

	private Boolean hasFalseOptionalConstraints;

	public boolean hasFalseOptionalConstraints() {
		if (hasFalseOptionalConstraints == null) {
			hasFalseOptionalConstraints = constraintProperties.stream().anyMatch(prop -> !prop.getFalseOptionalFeatures().isEmpty());
		}
		return hasFalseOptionalConstraints;
	}

	private Boolean hasVoidModelConstraints;

	public boolean hasVoidModelConstraints() {
		if (hasVoidModelConstraints == null) {
			hasVoidModelConstraints = testFor(ConstraintStatus.VOID) || testFor(ConstraintStatus.UNSATISFIABLE);
		}
		return hasVoidModelConstraints;
	}

	private Boolean hasRedundantConstraints;

	public boolean hasRedundantConstraints() {
		if (hasRedundantConstraints == null) {
			hasRedundantConstraints = testFor(ConstraintStatus.TAUTOLOGY) || testFor(ConstraintStatus.REDUNDANT);
		}
		return hasRedundantConstraints;
	}

}
