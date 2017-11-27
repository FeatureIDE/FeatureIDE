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

import java.util.Collection;

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

	private final Collection<FeatureProperties> featureProperties;
	private final Collection<ConstraintProperties> constraintProperties;

	public FeatureModelProperties(Collection<FeatureProperties> featureProperties, Collection<ConstraintProperties> constraintProperties) {
		this.featureProperties = featureProperties;
		this.constraintProperties = constraintProperties;
	}

	private Boolean hasFalseOptionalFeatures;

	public boolean hasFalseOptionalFeatures() {
		if (hasFalseOptionalFeatures == null) {
			for (final FeatureProperties f : featureProperties) {
				if (f.hasStatus(FeatureStatus.FALSE_OPTIONAL)) {
					hasFalseOptionalFeatures = Boolean.TRUE;
					break;
				}
			}
			hasFalseOptionalFeatures = Boolean.FALSE;
		}
		return hasFalseOptionalFeatures;
	}

	private Boolean hasDeadFeatures;

	public boolean hasDeadFeatures() {
		if (hasDeadFeatures == null) {
			for (final FeatureProperties f : featureProperties) {
				if (f.hasStatus(FeatureStatus.DEAD)) {
					hasDeadFeatures = Boolean.TRUE;
					break;
				}
			}
			hasDeadFeatures = Boolean.FALSE;
		}
		return hasDeadFeatures;
	}

	private Boolean hasIndeterminateHiddenFeatures;

	public boolean hasIndeterminateHiddenFeatures() {
		if (hasIndeterminateHiddenFeatures == null) {
			for (final FeatureProperties f : featureProperties) {
				if (f.hasStatus(FeatureStatus.INDETERMINATE_HIDDEN)) {
					hasIndeterminateHiddenFeatures = Boolean.TRUE;
					break;
				}
			}
			hasIndeterminateHiddenFeatures = Boolean.FALSE;
		}
		return hasIndeterminateHiddenFeatures;
	}

	private Boolean hasUnsatisfiableConstraints;

	public boolean hasUnsatisfiableConstraints() {
		if (hasUnsatisfiableConstraints == null) {
			for (final ConstraintProperties c : constraintProperties) {
				if (c.hasStatus(ConstraintStatus.UNSATISFIABLE)) {
					hasUnsatisfiableConstraints = Boolean.TRUE;
					break;
				}
			}
			hasUnsatisfiableConstraints = Boolean.FALSE;
		}
		return hasUnsatisfiableConstraints;
	}

	private Boolean hasTautologyConstraints;

	public boolean hasTautologyConstraints() {
		if (hasTautologyConstraints == null) {
			for (final ConstraintProperties c : constraintProperties) {
				if (c.hasStatus(ConstraintStatus.TAUTOLOGY)) {
					hasTautologyConstraints = Boolean.TRUE;
					break;
				}
			}
			hasTautologyConstraints = Boolean.FALSE;
		}
		return hasTautologyConstraints;
	}

	private Boolean hasDeadConstraints;

	public boolean hasDeadConstraints() {
		if (hasDeadConstraints == null) {
			for (final ConstraintProperties c : constraintProperties) {
				if (!c.getDeadFeatures().isEmpty()) {
					hasDeadConstraints = Boolean.TRUE;
					break;
				}
			}
			hasDeadConstraints = Boolean.FALSE;
		}
		return hasDeadConstraints;
	}

	private Boolean hasFalseOptionalConstraints;

	public boolean hasFalseOptionalConstraints() {
		if (hasFalseOptionalConstraints == null) {
			for (final ConstraintProperties c : constraintProperties) {
				if (!c.getFalseOptionalFeatures().isEmpty()) {
					hasFalseOptionalConstraints = Boolean.TRUE;
					break;
				}
			}
			hasFalseOptionalConstraints = Boolean.FALSE;
		}
		return hasFalseOptionalConstraints;
	}

	private Boolean hasVoidModelConstraints;

	public boolean hasVoidModelConstraints() {
		if (hasVoidModelConstraints == null) {
			for (final ConstraintProperties c : constraintProperties) {
				if (c.hasStatus(ConstraintStatus.VOID_MODEL) || c.hasStatus(ConstraintStatus.UNSATISFIABLE)) {
					hasVoidModelConstraints = Boolean.TRUE;
					break;
				}
			}
			hasVoidModelConstraints = Boolean.FALSE;
		}
		return hasVoidModelConstraints;
	}

	private Boolean hasRedundantConstraints;

	public boolean hasRedundantConstraints() {
		if (hasRedundantConstraints == null) {
			for (final ConstraintProperties c : constraintProperties) {
				if (c.hasStatus(ConstraintStatus.TAUTOLOGY) || c.hasStatus(ConstraintStatus.REDUNDANT)) {
					hasRedundantConstraints = Boolean.TRUE;
					break;
				}
			}
			hasRedundantConstraints = Boolean.FALSE;
		}
		return hasRedundantConstraints;
	}

}
