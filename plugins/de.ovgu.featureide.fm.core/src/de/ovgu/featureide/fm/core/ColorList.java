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
package de.ovgu.featureide.fm.core;

import java.util.ArrayList;

/**
 * Holds the colors for a feature.
 * 
 * @author Sebastian Krieter
 */
public class ColorList {
	public static final int INVALID_COLOR = -1;
	
	private final ColorschemeTable colorschemeTable;
	private final ArrayList<Integer> colors = new ArrayList<Integer>();
	
	public ColorList(Feature feature) {
		FeatureModel fm = feature.getFeatureModel();
		if (fm != null && fm.getColorschemeTable() != null) {
			colorschemeTable = fm.getColorschemeTable();
			for (int i = 0; i < colorschemeTable.size() + 1; i++) {
				colors.add(INVALID_COLOR);
			}
		} else {
			colorschemeTable = null;
		}
	}

	public static final boolean isValidColor(int color) {
		return color > INVALID_COLOR;
	}

	public boolean hasColor() {
		if (colorschemeTable == null) {
			return false;
		}
		return colors.get(colorschemeTable.getSelectedColorscheme()) > INVALID_COLOR;
	}
	
	public int getColor() {
		if (colorschemeTable == null) {
			return INVALID_COLOR;
		}
		return colors.get(colorschemeTable.getSelectedColorscheme());
	}
	
	public void setColor(int color) {
		if (colorschemeTable != null) {
			colors.set(colorschemeTable.getSelectedColorscheme(), color);
		}
	}
	
	public void removeColor() {
		if (colorschemeTable != null) {
			colors.set(colorschemeTable.getSelectedColorscheme(), INVALID_COLOR);
		}
	}
	
	
	public boolean hasColor(int scheme) {
		if (scheme >= colors.size()) {
			return false;
		}
		return colors.get(scheme) > INVALID_COLOR;
	}
	
	public int getColor(int scheme) {
		if (scheme >= colors.size()) {
			return INVALID_COLOR;
		}
		return colors.get(scheme);
	}
	
	public void setColor(int scheme, int color) {
		if (scheme < colors.size()) {
			colors.set(scheme, color);
		}
	}
	
	public void addColorscheme() {
		colors.add(INVALID_COLOR);
	}
	
	public void removeColorscheme() {
		if (colorschemeTable != null) {
			colors.remove(colorschemeTable.getSelectedColorscheme());
		}
	}

	public ColorList clone(Feature feature) {
		ColorList newColorScheme = new ColorList(feature);
		newColorScheme.colors.ensureCapacity(colors.size());
		for (Integer value : colors) {
			newColorScheme.colors.add(new Integer(value));
		}
		return newColorScheme;
	}
}
