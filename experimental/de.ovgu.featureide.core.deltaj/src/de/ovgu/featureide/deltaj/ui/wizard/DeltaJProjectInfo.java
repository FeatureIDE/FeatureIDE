/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.deltaj.ui.wizard;

import java.util.ArrayList;

import org.eclipse.xtext.ui.wizard.DefaultProjectInfo;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * @author Andr� Specht
 * Adapted for FeatureIDE by Sven Schuster
 */
public class DeltaJProjectInfo extends DefaultProjectInfo {
	private FeatureModel model;
	private ArrayList<Feature> selectedOptionalFeatures;
	private ArrayList<DOptFeature> combinedOptionalFeatures;
	private String modelPath;
	private boolean createsSeperateFiles;
	
	public FeatureModel getModel() {
		return model;
	}
	public void setModel(FeatureModel model) {
		this.model = model;
	}
	public ArrayList<Feature> getSelectedOptionalFeatures() {
		return selectedOptionalFeatures;
	}
	public void setSelectedOptionalFeatures(
			ArrayList<Feature> selectedOptionalFeatures) {
		this.selectedOptionalFeatures = selectedOptionalFeatures;
	}
	public String getModelPath() {
		return modelPath;
	}
	public void setModelPath(String modelPath) {
		this.modelPath = modelPath;
	}
	public boolean isCreatesSeperateFiles() {
		return createsSeperateFiles;
	}
	public void setCreatesSeperateFiles(boolean createsSeperateFiles) {
		this.createsSeperateFiles = createsSeperateFiles;
	}
	public ArrayList<DOptFeature> getCombinedOptionalFeatures() {
		return combinedOptionalFeatures;
	}
	public void setCombinedOptionalFeatures(ArrayList<DOptFeature> combinedOptionalFeatures) {
		this.combinedOptionalFeatures = combinedOptionalFeatures;
	}
	
}
