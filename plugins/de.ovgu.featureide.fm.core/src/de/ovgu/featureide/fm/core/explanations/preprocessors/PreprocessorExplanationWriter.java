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

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.explanations.ExplanationWriter;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationWriter;

/**
 * {@link ExplanationWriter} for instances of {@link PreprocessorExplanation}.
 *
 * @param <E> explanation
 * @author Timo G&uuml;nther
 */
public abstract class PreprocessorExplanationWriter<E extends PreprocessorExplanation<?>> extends FeatureModelExplanationWriter<E> {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param explanation explanation to transform
	 */
	protected PreprocessorExplanationWriter(E explanation) {
		super(explanation);
	}

	@Override
	protected String getConcreteReasonString(Reason<?> reason) {
		if (!(reason instanceof PreprocessorReason)) {
			return super.getConcreteReasonString(reason);
		}
		final Node expression = ((PreprocessorReason) reason).getSubject();
		return String.format("The expression is nested within a block annotated with %s.", expression.toString(getSymbols()));
	}
}
