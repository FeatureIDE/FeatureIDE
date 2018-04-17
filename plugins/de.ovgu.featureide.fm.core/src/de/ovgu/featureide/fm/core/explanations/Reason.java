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
package de.ovgu.featureide.fm.core.explanations;

import org.prop4j.Node;

/**
 * The atomic unit an explanation is composed of.
 *
 * @param <S> subject
 * @author Timo G&uuml;nther
 * @author Sofia Ananieva
 */
public abstract class Reason<S> implements Cloneable {

	/** The subject of this reason. */
	private final S subject;
	/** The containing explanation. */
	private final Explanation<?> explanation;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param reason the subject of this reason
	 * @param explanation the containing explanation
	 */
	protected Reason(S subject, Explanation<?> explanation) {
		this.subject = subject;
		this.explanation = explanation;
	}

	/**
	 * Returns the subject of this reason.
	 *
	 * @return the subject of this reason
	 */
	public S getSubject() {
		return subject;
	}

	/**
	 * Returns the containing explanation.
	 *
	 * @return the containing explanation
	 */
	public Explanation<?> getExplanation() {
		return explanation;
	}

	/**
	 * Returns the confidence of this reason. This is the likelihood with which this is causing the defect. Must be a value between 0 and 1.
	 *
	 * @return the confidence of this reason
	 */
	public float getConfidence() {
		float confidence = (float) getExplanation().getReasonCounts().get(this) / getExplanation().getExplanationCount();
		confidence = Math.max(0.0f, Math.min(1.0f, confidence)); // Clamp between 0 and 1 (just in case).
		return confidence;
	}

	/**
	 * Returns this reason as a node.
	 *
	 * @return this reason as a node
	 */
	public abstract Node toNode();

	@Override
	protected Reason<S> clone() {
		return clone(getExplanation());
	}

	/**
	 * Returns a copy of this with the given explanation.
	 *
	 * @param explanation explanation of the clone
	 * @return a copy of this with the given explanation
	 */
	protected abstract Reason<S> clone(Explanation<?> explanation);

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((subject == null) ? 0 : subject.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final Reason<?> other = (Reason<?>) obj;
		if (subject == null) {
			if (other.subject != null) {
				return false;
			}
		} else if (!subject.equals(other.subject)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName() + "[" + getSubject() + "]";
	}
}
