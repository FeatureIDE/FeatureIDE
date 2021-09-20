/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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

import de.ovgu.featureide.fm.core.base.IFeatureModelElement;

/**
 * {@link MultipleAnomaliesExplanationWriter} allows to write multiple explanations that make up an {@link MultipleAnomaliesExplanation}.
 *
 * @author Benedikt Jutz
 */
public class MultipleAnomaliesExplanationWriter extends FeatureModelExplanationWriter<MultipleAnomaliesExplanation> {

	/**
	 * Creates a new {@link MultipleAnomaliesExplanationWriter}.
	 *
	 * @param explanation - {@link MultipleAnomaliesExplanation}
	 */
	public MultipleAnomaliesExplanationWriter(MultipleAnomaliesExplanation explanation) {
		super(explanation);
	}

	/**
	 * The subject of this explanation is a whole feature model.
	 *
	 * @see de.ovgu.featureide.fm.core.explanations.ExplanationWriter#getSubjectString()
	 */
	@Override
	protected String getSubjectString() {
		return "Feature Model";
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.explanations.ExplanationWriter#getAttributeString()
	 */
	@Override
	protected String getAttributeString() {
		return "Anomalies";
	}

	/**
	 * Returns a special circumstances string for the given explanations.
	 *
	 * @see de.ovgu.featureide.fm.core.explanations.ExplanationWriter#getCircumstanceString()
	 */
	@Override
	public String getCircumstanceString() {
		return String.format("%s has the following %s", getSubjectString(), getAttributeString());
	}

	/**
	 * Returns the single explanations strings, separated by "---".
	 *
	 * @see de.ovgu.featureide.fm.core.explanations.ExplanationWriter#getReasonsString()
	 */
	@Override
	public String getReasonsString() {
		final StringBuilder reasonBuilder = new StringBuilder("\n");
		for (final FeatureModelExplanation<? extends IFeatureModelElement> singleExplanation : getExplanation().getSingleExplanations()) {
			reasonBuilder.append("---\n");
			reasonBuilder.append(singleExplanation.getWriter().getString());
		}
		return reasonBuilder.toString();
	}
}
