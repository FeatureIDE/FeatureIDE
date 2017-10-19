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
package de.ovgu.featureide.fm.core.explanations.preprocessors;

import de.ovgu.featureide.fm.core.explanations.ExplanationWriter;

/**
 * {@link ExplanationWriter} for {@link InvariantPresenceConditionExplanation}.
 *
 * @author Timo G&uuml;nther
 */
public class InvariantPresenceConditionExplanationWriter extends PreprocessorExplanationWriter<InvariantPresenceConditionExplanation> {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param explanation explanation to transform
	 */
	public InvariantPresenceConditionExplanationWriter(InvariantPresenceConditionExplanation explanation) {
		super(explanation);
	}

	@Override
	protected String getSubjectString() {
		return String.format("presence condition of %s", getExplanation().getSubject().toString(getSymbols()));
	}

	@Override
	protected String getAttributeString() {
		return getExplanation().isTautology() ? "a tautology" : "a contradiction";
	}
}
