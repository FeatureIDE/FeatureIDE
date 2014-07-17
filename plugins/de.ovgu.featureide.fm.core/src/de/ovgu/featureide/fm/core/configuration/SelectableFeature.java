/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import de.ovgu.featureide.fm.core.Feature;

/**
 * A representation of a selectable feature for the configuration process.
 */
public class SelectableFeature extends TreeElement {

	private Selection manual = Selection.UNDEFINED;

	private Selection automatic = Selection.UNDEFINED;

	private final Feature feature;

	private final Configuration configuration;

	private String name;

	public SelectableFeature(Configuration configuration, Feature feature) {
		this.configuration = configuration;
		this.feature = feature;
	}

	public Selection getSelection() {
		return automatic == Selection.UNDEFINED ? manual : automatic;
	}

	public Selection getManual() {
		return manual;
	}

	protected void setManual(Selection manual) {
		if (manual == Selection.UNDEFINED || automatic == Selection.UNDEFINED) {
			this.manual = manual;
		} else if (manual != automatic) {
			throw new SelectionNotPossibleException(feature.getName(), manual);
		}
	}

	public Selection getAutomatic() {
		return automatic;
	}

	protected void setAutomatic(Selection automatic) {
		if (automatic == Selection.UNDEFINED || manual == Selection.UNDEFINED || manual == automatic) {
			this.automatic = automatic;
		} else {
			throw new AutomaticalSelectionNotPossibleException(feature.getName(), automatic);
		}
	}

	public String getName() {
		if (name != null) {
			return name;
		}
		return feature == null ? null : feature.getName();
	}

	public Feature getFeature() {
		return feature;
	}
	
	public Configuration getConfiguration() {
		return configuration;
	}

	public String toString() {
		return getName();
	}

	public void setName(String name) {
		this.name = name;
	}

}
