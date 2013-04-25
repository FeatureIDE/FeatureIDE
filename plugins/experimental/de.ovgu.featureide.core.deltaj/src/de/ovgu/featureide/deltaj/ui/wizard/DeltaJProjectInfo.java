package de.ovgu.featureide.deltaj.ui.wizard;

import java.util.ArrayList;

import org.eclipse.xtext.ui.wizard.DefaultProjectInfo;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

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
