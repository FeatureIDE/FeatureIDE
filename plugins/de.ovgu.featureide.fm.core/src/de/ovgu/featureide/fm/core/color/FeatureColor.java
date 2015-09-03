/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

/**
 * A mapping from colors to indexes.
 * 
 * @author Jens Meinicke
 */
public enum FeatureColor {
	NO_COLOR(-1), RED(0), ORANGE(1), YELLOW(2), DARK_GREEN(3), LIGHT_GREEN(4), CYAN(5), LIGHT_GRAY(6), BLUE(7), MAGENTA(8), PINK(9);
	
	final int value;
	FeatureColor(int i) {
		this.value = i;
	}
	
	public int getValue() {
		return value;
	}

	public static FeatureColor getColor(int index) {
		for (FeatureColor c : values()) {
			if (c.value == index) {
				return c;
			}
		}
		throw new RuntimeException("Color " + index + " not found");
	}
}