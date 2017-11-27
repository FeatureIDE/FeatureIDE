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
package de.ovgu.featureide.fm.core.explanations.config;

import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.explanations.ExplanationWriter;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationWriter;

/**
 * {@link ExplanationWriter} for instances of {@link ConfigurationExplanation}.
 *
 * @param <E> explanation
 * @author Timo G&uuml;nther
 */
public abstract class ConfigurationExplanationWriter<E extends ConfigurationExplanation<?>> extends FeatureModelExplanationWriter<E> {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param explanation explanation to transform
	 */
	public ConfigurationExplanationWriter(E explanation) {
		super(explanation);
	}

	@Override
	protected String getConcreteReasonString(Reason<?> reason) {
		if (!(reason instanceof ConfigurationReason)) {
			return super.getConcreteReasonString(reason);
		}
		final SelectableFeature selection = ((ConfigurationReason) reason).getSubject();
		String selectionString;
		switch (selection.getSelection()) {
		case SELECTED:
			selectionString = "selected";
			break;
		case UNSELECTED:
			selectionString = "unselected";
			break;
		case UNDEFINED:
			selectionString = "neither selected nor unselected";
		default:
			throw new IllegalStateException("Unknown feature selection state");
		}
		switch (selection.getManual()) {
		case SELECTED:
		case UNSELECTED:
			selectionString = String.format("manually %s", selectionString);
			break;
		case UNDEFINED:
			break;
		default:
			throw new IllegalStateException("Unknown feature selection state");
		}
		return String.format("%s is %s.", selection.getFeature().getName(), selectionString);
	}
}
