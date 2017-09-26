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

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;

/**
 * An explanation for an automatic selection in a configuration.
 *
 * @author Timo G&uuml;nther
 */
public class AutomaticSelectionExplanation extends ConfigurationExplanation {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param subject the subject to be explained
	 */
	public AutomaticSelectionExplanation(SelectableFeature subject, Configuration config) {
		super(subject, config);
	}

	@Override
	public SelectableFeature getSubject() {
		return (SelectableFeature) super.getSubject();
	}

	@Override
	public AutomaticSelectionExplanationWriter getWriter() {
		return new AutomaticSelectionExplanationWriter(this);
	}
}
