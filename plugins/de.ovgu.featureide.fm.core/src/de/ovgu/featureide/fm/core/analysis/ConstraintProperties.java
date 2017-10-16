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
import java.util.Collections;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.explanations.Explanation;

/**
 * Represents a propositional constraint below the feature diagram.
 *
 * @author Sebastian Krieter
 */
public class ConstraintProperties {

	public enum ConstraintRedundancyStatus {
		UNKNOWN, NORMAL, REDUNDANT, IMPLICIT, TAUTOLOGY
	}

	public enum ConstraintDeadStatus {
		UNKNOWN, NORMAL, DEAD
	}

	public enum ConstraintFalseOptionalStatus {
		UNKNOWN, NORMAL, FALSE_OPTIONAL
	}

	public enum ConstraintFalseSatisfiabilityStatus {
		UNKNOWN, SATISFIABLE, VOID_MODEL, UNSATISFIABLE
	}

	private ConstraintRedundancyStatus constraintRedundancyStatus = ConstraintRedundancyStatus.UNKNOWN;
	private ConstraintDeadStatus constraintDeadStatus = ConstraintDeadStatus.UNKNOWN;
	private ConstraintFalseOptionalStatus constraintFalseOptionalStatus = ConstraintFalseOptionalStatus.UNKNOWN;
	private ConstraintFalseSatisfiabilityStatus constraintSatisfiabilityStatus = ConstraintFalseSatisfiabilityStatus.UNKNOWN;

	protected Collection<IFeature> deadFeatures = Collections.emptyList();
	protected Collection<IFeature> falseOptionalFeatures = Collections.emptyList();

	/**
	 * Explanation for redundant constraints.
	 */
	private Explanation redundantExplanation;

	private final IConstraint constraint;

	public ConstraintProperties(IConstraint constraint) {
		this.constraint = constraint;
	}

	public boolean hasStatus(ConstraintRedundancyStatus constraintRedundancyStatus) {
		return this.constraintRedundancyStatus == constraintRedundancyStatus;
	}

	public boolean hasStatus(ConstraintDeadStatus constraintDeadStatus) {
		return this.constraintDeadStatus == constraintDeadStatus;
	}

	public boolean hasStatus(ConstraintFalseOptionalStatus constraintFalseOptionalStatus) {
		return this.constraintFalseOptionalStatus == constraintFalseOptionalStatus;
	}

	public boolean hasStatus(ConstraintFalseSatisfiabilityStatus constraintFalseSatisfiabilityStatus) {
		return constraintSatisfiabilityStatus == constraintFalseSatisfiabilityStatus;
	}

	public Collection<IFeature> getDeadFeatures() {
		return Collections.unmodifiableCollection(deadFeatures);
	}

	public Collection<IFeature> getFalseOptionalFeatures() {
		return falseOptionalFeatures;
	}

	public void setFalseOptionalFeatures(Collection<IFeature> falseOptionalFeatures) {
		this.falseOptionalFeatures = falseOptionalFeatures;
	}

	public IConstraint getConstraint() {
		return constraint;
	}

	public void setDeadFeatures(Collection<IFeature> deadFeatures) {
		this.deadFeatures = deadFeatures;
	}

	public Explanation getRedundantExplanation() {
		return redundantExplanation;
	}

	public void setRedundantExplanation(Explanation redundantExplanation) {
		this.redundantExplanation = redundantExplanation;
	}

	public ConstraintRedundancyStatus getConstraintRedundancyStatus() {
		return constraintRedundancyStatus;
	}

	public void setConstraintRedundancyStatus(ConstraintRedundancyStatus constraintRedundancyStatus) {
		this.constraintRedundancyStatus = constraintRedundancyStatus;
	}

	public ConstraintDeadStatus getConstraintDeadStatus() {
		return constraintDeadStatus;
	}

	public void setConstraintDeadStatus(ConstraintDeadStatus constraintDeadStatus) {
		this.constraintDeadStatus = constraintDeadStatus;
	}

	public ConstraintFalseOptionalStatus getConstraintFalseOptionalStatus() {
		return constraintFalseOptionalStatus;
	}

	public void setConstraintFalseOptionalStatus(ConstraintFalseOptionalStatus constraintFalseOptionalStatus) {
		this.constraintFalseOptionalStatus = constraintFalseOptionalStatus;
	}

	public ConstraintFalseSatisfiabilityStatus getConstraintSatisfiabilityStatus() {
		return constraintSatisfiabilityStatus;
	}

	public void setConstraintSatisfiabilityStatus(ConstraintFalseSatisfiabilityStatus constraintFalseSatisfiabilityStatus) {
		constraintSatisfiabilityStatus = constraintFalseSatisfiabilityStatus;
	}

	public void resetStatus() {
		constraintRedundancyStatus = ConstraintRedundancyStatus.UNKNOWN;
		constraintDeadStatus = ConstraintDeadStatus.UNKNOWN;
		constraintFalseOptionalStatus = ConstraintFalseOptionalStatus.UNKNOWN;
		constraintSatisfiabilityStatus = ConstraintFalseSatisfiabilityStatus.UNKNOWN;
	}

}
