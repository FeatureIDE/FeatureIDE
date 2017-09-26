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

/**
 * The atomic unit an explanation is composed of.
 *
 * @author Timo G&uuml;nther
 * @author Sofia Ananieva
 */
public abstract class Reason implements Cloneable {

	/** The containing explanation. */
	private Explanation explanation;

	/**
	 * Constructs a new instance of this class.
	 */
	public Reason() {}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param reason reason to clone
	 */
	protected Reason(Reason reason) {
		setExplanation(reason.getExplanation());
	}

	/**
	 * Returns the containing explanation.
	 *
	 * @return the containing explanation; not null
	 */
	public Explanation getExplanation() {
		return explanation;
	}

	/**
	 * Sets the containing explanation. Does not actually add this reason to the given explanation.
	 *
	 * @param explanation the containing explanation; not null
	 */
	protected void setExplanation(Explanation explanation) {
		this.explanation = explanation;
	}

	/**
	 * Returns the confidence of this reason. This is the likelihood with which this is causing the defect. Should be a value between 0 and 1.
	 *
	 * @return the confidence of this reason
	 */
	public float getConfidence() {
		float confidence = (float) explanation.getReasonCounts().get(this) / explanation.getExplanationCount();
		confidence = Math.max(0.0f, Math.min(1.0f, confidence)); // Clamp between 0 and 1 (just in case).
		return confidence;
	}

	@Override
	protected abstract Reason clone();

	@Override
	public String toString() {
		return explanation.getWriter().getReasonString(this);
	}
}
