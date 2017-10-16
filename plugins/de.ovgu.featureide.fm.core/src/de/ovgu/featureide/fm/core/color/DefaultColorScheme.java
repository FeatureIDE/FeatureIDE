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

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * The color scheme that cannot hold any colors.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class DefaultColorScheme extends ColorScheme {

	public static String defaultName = DefaultColorScheme.class.getName();

	public DefaultColorScheme() {
		super(defaultName);
		setCurrent(true);
	}

	@Override
	public boolean isDefault() {
		return true;
	}

	@Override
	public void setColor(IFeature feature, FeatureColor color) {
		throw new RuntimeException("setColor called on default color scheme");
	}

	@Override
	public FeatureColor getColor(IFeature feature) {
		return FeatureColor.NO_COLOR;
	}

	@Override
	public void renameFeature(String oldName, String newName) {
		// nothing here
	}
}
