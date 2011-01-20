/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import de.ovgu.featureide.fm.core.Feature;

public class SelectableFeature extends TreeElement {

	private Selection manual = Selection.UNDEFINED;

	private Selection automatic = Selection.UNDEFINED;

	private Feature feature;

	private Configuration configuration;

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
		if (manual == Selection.UNDEFINED || automatic == Selection.UNDEFINED)
			this.manual = manual;
		else if (manual != automatic)
			throw new SelectionNotPossibleException(feature.getName(), manual);
	}

	public Selection getAutomatic() {
		return automatic;
	}

	protected void setAutomatic(Selection automatic) {
		if (automatic == Selection.UNDEFINED || manual == Selection.UNDEFINED || manual == automatic)
			this.automatic = automatic;
		else
			throw new AutomaticalSelectionNotPossibleException(feature.getName(), automatic);
	}

	public String getName() {
		if (name != null)
			return name;
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
