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

import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintDeadStatus;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintFalseSatisfiabilityStatus;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintRedundancyStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureDeterminedStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureParentStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureSelectionStatus;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * All additional properties of an {@link IFeature}.
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class FeatureModelProperties {

	protected final IFeatureModel featureModel;

	private final Collection<FeatureProperties> featureProperties;
	private final Collection<ConstraintProperties> constraintProperties;

	protected FeatureStatus status = FeatureStatus.NORMAL;

	public FeatureModelProperties(IFeatureModel featureModel, Collection<FeatureProperties> featureProperties,
			Collection<ConstraintProperties> constraintProperties) {
		this.featureModel = featureModel;
		this.featureProperties = featureProperties;
		this.constraintProperties = constraintProperties;
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public FeatureStatus getFeatureStatus() {
		return status;
	}

	public void setFeatureStatus(FeatureStatus status) {
		this.status = status;
	}

	public boolean hasFalseOptionalFeatures() {
		for (final FeatureProperties f : featureProperties) {
			if (f.getFeatureParentStatus() == FeatureParentStatus.FALSE_OPTIONAL) {
				return true;
			}
		}
		return false;
	}

	public boolean hasDeadFeatures() {
		for (final FeatureProperties f : featureProperties) {
			if (f.getFeatureSelectionStatus() == FeatureSelectionStatus.DEAD) {
				return true;
			}
		}
		return false;
	}
	
	public boolean hasIndeterminateHiddenFeatures() {
		for (final FeatureProperties f : featureProperties) {
			if (f.getFeatureDeterminedStatus() == FeatureDeterminedStatus.INDETERMINATE_HIDDEN) {
				return true;
			}
		}
		return false;
	}

	public boolean hasUnsatisfiableConstraints() {
		for (final ConstraintProperties c : constraintProperties) {
			if (c.getConstraintSatisfiabilityStatus() == ConstraintFalseSatisfiabilityStatus.UNSATISFIABLE) {
				return true;
			}
		}
		return false;
	}

	public boolean hasTautologyConstraints() {
		for (final ConstraintProperties c : constraintProperties) {
			if (c.getConstraintRedundancyStatus() == ConstraintRedundancyStatus.TAUTOLOGY) {
				return true;
			}
		}
		return false;
	}

	public boolean hasDeadConstraints() {
		for (final ConstraintProperties c : constraintProperties) {
			if (c.getConstraintDeadStatus() == ConstraintDeadStatus.DEAD) {
				return true;
			}
		}
		return false;
	}

	public boolean hasVoidModelConstraints() {
		for (final ConstraintProperties c : constraintProperties) {
			final ConstraintFalseSatisfiabilityStatus constraintSatisfiabilityStatus = c.getConstraintSatisfiabilityStatus();
			if (constraintSatisfiabilityStatus == ConstraintFalseSatisfiabilityStatus.VOID_MODEL || constraintSatisfiabilityStatus == ConstraintFalseSatisfiabilityStatus.UNSATISFIABLE) {
				return true;
			}
		}
		return false;
	}

	public boolean hasRedundantConstraints() {
		for (final ConstraintProperties c : constraintProperties) {
			final ConstraintRedundancyStatus constraintRedundancyStatus = c.getConstraintRedundancyStatus();
			if (constraintRedundancyStatus == ConstraintRedundancyStatus.TAUTOLOGY || constraintRedundancyStatus == ConstraintRedundancyStatus.REDUNDANT) {
				return true;
			}
		}
		return false;
	}

}
