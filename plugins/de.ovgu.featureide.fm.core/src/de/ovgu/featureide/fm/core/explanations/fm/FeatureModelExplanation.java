/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.explanations.fm;

import java.util.LinkedHashSet;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.Reason;

/**
 * An explanation created by {@link FeatureModelExplanationCreator}.
 *
 * @param <S> subject
 * @author Timo G&uuml;nther
 */
public abstract class FeatureModelExplanation<S> extends Explanation<S> {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param subject the subject to be explained
	 */
	protected FeatureModelExplanation(S subject) {
		super(subject);
	}

	/**
	 * Returns all feature model elements affected by this explanation. An element is considered affected if it is the defect element, the source element of any
	 * reason or part of any such constraint.
	 *
	 * @return all feature model elements affected by this explanation
	 */
	public Set<IFeatureModelElement> getAffectedElements() {
		final Set<IFeatureModelElement> affectedElements = new LinkedHashSet<>();
		for (final Reason<?> reason : getReasons()) {
			if (!(reason instanceof FeatureModelReason)) {
				continue;
			}
			affectedElements.addAll(((FeatureModelReason) reason).getSubject().getElements());
		}
		if (getSubject() instanceof IFeatureModelElement) {
			affectedElements.add((IFeatureModelElement) getSubject());
		}
		final Set<IFeatureModelElement> constraintElements = new LinkedHashSet<>();
		for (final IFeatureModelElement affectedElement : affectedElements) {
			if (!(affectedElement instanceof IConstraint)) {
				continue;
			}
			final IConstraint constraint = (IConstraint) affectedElement;
			constraintElements.addAll(constraint.getContainedFeatures());
		}
		affectedElements.addAll(constraintElements);
		return affectedElements;
	}

	/**
	 * Returns all features affected by this explanation.
	 *
	 * @return all features affected by this explanation
	 */
	public Set<IFeature> getAffectedFeatures() {
		final Set<IFeature> affectedFeatures = new LinkedHashSet<>();
		for (final IFeatureModelElement affectedElement : getAffectedElements()) {
			if (affectedElement instanceof IFeature) {
				affectedFeatures.add((IFeature) affectedElement);
			}
		}
		return affectedFeatures;
	}

	/**
	 * Returns all constraints affected by this explanation.
	 *
	 * @return all constraints affected by this explanation
	 */
	public Set<IConstraint> getAffectedConstraints() {
		final Set<IConstraint> affectedConstraints = new LinkedHashSet<>();
		for (final IFeatureModelElement affectedElement : getAffectedElements()) {
			if (affectedElement instanceof IConstraint) {
				affectedConstraints.add((IConstraint) affectedElement);
			}
		}
		return affectedConstraints;
	}
}
