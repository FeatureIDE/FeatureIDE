/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.cloneanalysis.views;

public enum CloneVariantType {
	/**
	 * Crossvariant clone, found in different projects
	 */
	CROSSPROJECT("inter-feature"), // TODO revert to "inter-project".
	/**
	 * Crossvariant clone, found in different feature folders
	 */
	CROSSFEATURE("inter-feature"),
	/**
	 * Intravariant clone. All found occurences are within the same featurefolder / project.
	 */
	INTRAVARIANT("intra-feature"),
	/**
	 * Variant type not determined (yet).
	 */
	UNDEFINED("undefined");

	private String viewString;

	private CloneVariantType(String viewString) {
		this.viewString = viewString;
	}

	@Override
	public String toString() {
		return viewString;
	}
}
