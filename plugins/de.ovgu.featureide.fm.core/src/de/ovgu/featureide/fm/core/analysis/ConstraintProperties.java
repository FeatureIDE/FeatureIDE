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
import java.util.Collections;
import java.util.EnumSet;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.explanations.Explanation;

/**
 * Represents a propositional constraint below the feature diagram.
 *
 * @author Sebastian Krieter
 */
public class ConstraintProperties {

	public enum ConstraintStatus {
		NECESSARY, REDUNDANT, IMPLICIT, TAUTOLOGY, SATISFIABLE, VOID_MODEL, UNSATISFIABLE
	}

	private static final EnumSet<ConstraintStatus> constraintRedundancyStatus =
		EnumSet.of(ConstraintStatus.NECESSARY, ConstraintStatus.REDUNDANT, ConstraintStatus.IMPLICIT, ConstraintStatus.TAUTOLOGY);
	private static final EnumSet<ConstraintStatus> constraintSatisfiabilityStatus =
		EnumSet.of(ConstraintStatus.SATISFIABLE, ConstraintStatus.VOID_MODEL, ConstraintStatus.UNSATISFIABLE);

	private final EnumSet<ConstraintStatus> constraintStatus = EnumSet.noneOf(ConstraintStatus.class);

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

	public boolean hasStatus(ConstraintStatus constraintStatus) {
		return this.constraintStatus.contains(constraintStatus);
	}

	public void setStatus(ConstraintStatus constraintStatus) {
		if (constraintSatisfiabilityStatus.contains(constraintStatus)) {
			this.constraintStatus.removeAll(constraintSatisfiabilityStatus);
		} else if (constraintRedundancyStatus.contains(constraintStatus)) {
			this.constraintStatus.removeAll(constraintRedundancyStatus);
		}
		this.constraintStatus.add(constraintStatus);
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

	public void setDeadFeatures(Collection<IFeature> deadFeatures) {
		this.deadFeatures = deadFeatures;
	}

	public IConstraint getConstraint() {
		return constraint;
	}

	public Explanation getRedundantExplanation() {
		return redundantExplanation;
	}

	public void setRedundantExplanation(Explanation redundantExplanation) {
		this.redundantExplanation = redundantExplanation;
	}

	public void resetStatus() {
		constraintStatus.clear();
	}

}
