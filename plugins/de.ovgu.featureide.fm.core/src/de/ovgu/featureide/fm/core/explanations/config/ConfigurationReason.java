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
import de.ovgu.featureide.fm.core.explanations.Reason;

/**
 * A reason of an explanation involving a configuration.
 *
 * @author Timo G&uuml;nther
 */
public class ConfigurationReason extends Reason {

	/** The feature that has been selected or unselected. */
	private final SelectableFeature featureSelection;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param featureSelection the feature that has been selected or unselected; not null
	 */
	public ConfigurationReason(SelectableFeature featureSelection) {
		this.featureSelection = featureSelection;
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param reason the reason to clone; not null
	 */
	protected ConfigurationReason(ConfigurationReason reason) {
		super(reason);
		featureSelection = reason.featureSelection;
	}

	/**
	 * Returns the feature that has been selected or unselected.
	 *
	 * @return the feature that has been selected or unselected; not null
	 */
	public SelectableFeature getFeatureSelection() {
		return featureSelection;
	}

	@Override
	protected ConfigurationReason clone() {
		return new ConfigurationReason(featureSelection);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((featureSelection == null) ? 0 : featureSelection.hashCode());
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
		final ConfigurationReason other = (ConfigurationReason) obj;
		if (featureSelection == null) {
			if (other.featureSelection != null) {
				return false;
			}
		} else if (!featureSelection.equals(other.featureSelection)) {
			return false;
		}
		return true;
	}
}
