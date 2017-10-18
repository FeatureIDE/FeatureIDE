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
package de.ovgu.featureide.fm.core.color;

import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Saves colors for features.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class ColorScheme {

	/**
	 * The unique name of the scheme.
	 */
	private String name;

	/**
	 * Specifies whether the scheme is active-
	 */
	private boolean isCurrent = false;

	private final Map<String, FeatureColor> colors = new HashMap<>();

	public ColorScheme(String name) {
		this.name = name;
	}

	/**
	 * Returns the color scheme.
	 */
	public Map<String, FeatureColor> getColors() {
		return colors;
	}

	/**
	 *
	 * @return The name of the scheme.
	 */
	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public boolean isCurrent() {
		return isCurrent;
	}

	/**
	 * Returns whether the scheme is the default scheme.
	 */
	public boolean isDefault() {
		return false;
	}

	/**
	 * Sets the color of the given feature.
	 */
	public void setColor(IFeature feature, FeatureColor color) {
		setColor(feature.getName(), color);
	}

	/**
	 * Sets the color of the given feature.
	 */
	public void setColor(String feature, FeatureColor color) {
		colors.put(feature, color);
	}

	/**
	 * Returns the color of the given feature.
	 */
	public FeatureColor getColor(IFeature feature) {
		if (colors.containsKey(feature.getName())) {
			return colors.get(feature.getName());
		}
		return FeatureColor.NO_COLOR;
	}

	/**
	 * Activates the scheme.
	 */
	public void setCurrent(boolean current) {
		isCurrent = current;
	}

	public void renameFeature(String oldName, String newName) {
		if (colors.containsKey(oldName)) {
			colors.put(newName, colors.remove(oldName));
		}
	}

	@Override
	public String toString() {
		return name + ":" + (isCurrent ? "ACTIVE" : "INACTIV") + "  " + colors;
	}
}
