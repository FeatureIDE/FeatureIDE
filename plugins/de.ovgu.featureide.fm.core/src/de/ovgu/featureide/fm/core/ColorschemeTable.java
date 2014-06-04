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

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlColorModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlColorModelWriter;

/** 
 * Holds the color scheme names for a {@link FeatureModel}.
 * 
 * @author Sebastian Krieter
 */
public class ColorschemeTable {
	private static final String DEFAULT_COLORSCHEMENAME = "Default Colorscheme";
	private static final String COLOR_FILE_NAME = ".color.xml";
	
	private final FeatureModel featureModel;
	
	private ArrayList<String> colorschemeNames = new ArrayList<String>();
	private int selectedColorscheme;
	
	/**
	 * @param featureModel
	 */
	public ColorschemeTable(FeatureModel featureModel) {
		this.featureModel = featureModel;
		reset();
	}

	/**
	 * @return colorscheme names without the first empty one
	 */
	public List<String> getColorschemeNames() {
		return colorschemeNames.subList(1, colorschemeNames.size());
	}

	/**
	 * @param name the new colorscheme name
	 */
	public void addColorscheme(String name) {
		colorschemeNames.add(name);
		for (Feature feat : featureModel.getFeatureTable().values()) {
			feat.getColorList().addColorscheme();
		}
	}
	
	/**
	 * Removes the current Colorscheme.
	 */
	public void removeColorscheme() {
		if (colorschemeNames.size() == 2) {
			colorschemeNames.set(1, DEFAULT_COLORSCHEMENAME);
			for (Feature feat : featureModel.getFeatureTable().values()) {
				feat.getColorList().removeColor();
			}
		} else {
			colorschemeNames.remove(selectedColorscheme);
			for (Feature feat : featureModel.getFeatureTable().values()) {
				feat.getColorList().removeColorscheme();
			}
			if (selectedColorscheme == colorschemeNames.size()) {
				selectedColorscheme--;
			}
		}
	}
	
	/**
	 * Renames the current colorscheme.
	 * 
	 * @param name the new name
	 */
	public void renameColorscheme(String name) {
		colorschemeNames.set(selectedColorscheme, name);
	}

	/**
	 * @return the number of valid colorschemes
	 */
	public int size() {
		return colorschemeNames.size() - 1;
	}

	/**
	 * @return the selected colorscheme
	 */
	public int getSelectedColorscheme() {
		return selectedColorscheme;
	}
	
	public String getSelectedColorschemeName() {
		if (selectedColorscheme == 0) {
			return null;
		}
		return colorschemeNames.get(selectedColorscheme);
	}
	
	/**
	 * @param colorscheme
	 */
	public void setSelectedColorscheme(int colorscheme) {
		this.selectedColorscheme = colorscheme;
	}
	
	/**
	 * Sets the selected colorscheme to an empty colorschme
	 */
	public void setEmptyColorscheme() {
		this.selectedColorscheme = 0;
	}
	
	public void reset() {
		colorschemeNames.clear();
		colorschemeNames.add("");
		colorschemeNames.add(DEFAULT_COLORSCHEMENAME);
		selectedColorscheme = 1;
	}
	
	public void clearBeforeLoading() {
		colorschemeNames.clear();
		colorschemeNames.add("");
		selectedColorscheme = 0;
	}
	
	public void checkAfterLoading() {
		if (colorschemeNames.size() < 2) {
			colorschemeNames.add(DEFAULT_COLORSCHEMENAME);
			selectedColorscheme = 1;
		}
	}
	
	/**
	 * Method to save all assigned colors and colorschemes to the color.xml file
	 */
	public void saveColorsToFile(IProject project) {
		try {
			FeatureModelWriterIFileWrapper w = new FeatureModelWriterIFileWrapper(new XmlColorModelWriter(featureModel));
			w.writeToFile(getColorFile(project));
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	public IFile getColorFile(IProject project) {
		return project.getFile(COLOR_FILE_NAME);
	}
	
	/**
	 * Method to read color schemes and colors from the color.xml file
	 */
	public void readColorsFromFile(IProject project) {
		IFile file = getColorFile(project);
		if (file != null && file.exists()) {
			try {
				FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(new XmlColorModelReader(featureModel));
				reader.readFromFile(file);
			} catch (FileNotFoundException e) {
				FMCorePlugin.getDefault().logError(e);
			} catch (UnsupportedModelException e) {
				FMCorePlugin.getDefault().logError(e);
			}
		}
	}
	
	public ColorschemeTable clone(FeatureModel fm) {
		ColorschemeTable newColorSchemeProvider = new ColorschemeTable(fm);
		
		newColorSchemeProvider.colorschemeNames = new ArrayList<String>(colorschemeNames);
		newColorSchemeProvider.selectedColorscheme = selectedColorscheme;
		
		return newColorSchemeProvider;
	}
}
