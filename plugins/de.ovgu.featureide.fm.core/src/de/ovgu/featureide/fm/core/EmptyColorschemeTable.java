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
package de.ovgu.featureide.fm.core;

import java.util.List;

import org.eclipse.core.resources.IProject;

/** 
 * Holds the color scheme names for a {@link FeatureModel}.
 * 
 * @author Sebastian Krieter
 */
public class EmptyColorschemeTable extends ColorschemeTable {

	public EmptyColorschemeTable() {
		super();
	}

	@Override
	public List<String> getColorschemeNames() {
		return colorschemeNames;
	}

	@Override
	public void addColorscheme(String name) {
	}

	@Override
	public void removeColorscheme() {
	}

	@Override
	public void renameColorscheme(String name) {
	}

	@Override
	public int size() {
		return 0;
	}

	@Override
	public String getSelectedColorschemeName() {
		return "";
	}

	@Override
	public void setSelectedColorscheme(int colorscheme) {
	}

	@Override
	public void setEmptyColorscheme() {
	}

	@Override
	public void reset() {
	}

	@Override
	public void clearBeforeLoading() {
	}

	@Override
	public void checkAfterLoading() {
	}

	@Override
	public void saveColorsToFile(IProject project) {
	}
	
	@Override
	public void readColorsFromFile(IProject project) {
	}

	@Override
	public ColorschemeTable clone(FeatureModel fm) {
		return new EmptyColorschemeTable();
	}
	
}
