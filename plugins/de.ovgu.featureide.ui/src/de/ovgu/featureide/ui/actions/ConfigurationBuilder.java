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
package de.ovgu.featureide.ui.actions;

import java.util.LinkedList;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Builds all valid configurations for a selected feature project.
 * 
 * @author Jens Meinicke
 */
public class ConfigurationBuilder {

	private final static String JOB_TITLE = "Build all valid configurations";
	private final static String SUBTASK_BUILD = "Build Configuration ";
	private static final String SUBTASK_GET = "Get Configuration ";
	private final static String CONFIGURATION_NAME = "Variant";
	final static String FOLDER_NAME = "products";
	
	private IFeatureProject project;
	private IFolder folder;
	private FeatureModel featureModel;
	private LinkedList<String> layer;
	private Configuration configuration;
	private ConfigurationReader reader;
	private long confs;
	private String zeros;
	private int configurationNumber = 0;
	private boolean counting = true;
	
	ConfigurationBuilder(IFeatureProject featureProject) {
		project = featureProject;
		featureModel = project.getFeatureModel();
		
		Job number = new Job("Count configurations") {
			public IStatus run(IProgressMonitor monitor) {
				configurationNumber = (int)new Configuration(featureModel, false, false).number(1000000);
				return Status.OK_STATUS;
			}
		};
		number.setPriority(Job.LONG);
		number.schedule();
		
		Job job = new Job(JOB_TITLE) {
			public IStatus run(IProgressMonitor monitor) {
				try {
					long time = System.currentTimeMillis();
					monitor.beginTask("" , 1);
					
					init(monitor);
					
					monitor.subTask(SUBTASK_GET + confs + "/" + (configurationNumber == 0 ? "counting..." : configurationNumber));
					buildAll(featureModel.getRoot(), monitor);
					
					try {
						folder.refreshLocal(IResource.DEPTH_INFINITE, null);
					} catch (CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
					
					time = System.currentTimeMillis() - time;
					long s = (time/1000)%60;
					long min = (time/(60 * 1000))%60;
					long h = time/(60 * 60 * 1000);
					String t = h + "h " + (min < 10 ? "0" + min : min) + "min " + (s < 10 ? "0" + s : s) + "s.";
					UIPlugin.getDefault().logInfo(confs-1 + (configurationNumber != 0 ? " of " + configurationNumber : "") + " configurations built in " + t);
				} finally {
					monitor.done();
				}
				return Status.OK_STATUS;
			}

			
			
		};
		job.setPriority(Job.LONG);
		job.schedule();
	}
	

	private void init(IProgressMonitor monitor) {
		confs = 1;
		folder = project.getProject().getFolder(FOLDER_NAME);
		if (!folder.exists()) {
			try {
				folder.create(true, true, null);
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		} else {
			try {
				int countProducts = folder.members().length;
				int current = 1;
				for (IResource res : folder.members()) {
					monitor.subTask("Remove old products : " + current + "/" + countProducts);
					current++;
					res.delete(true, null);
				}
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		}
		layer = new LinkedList<String>();
		for (String feature : featureModel.getLayerNames()) {
				layer.add(feature);
		}
		configuration = new Configuration(featureModel);
		reader = new ConfigurationReader(configuration);
		project.getComposer().initialize(project);
	}
	
	private void buildAll(Feature root, IProgressMonitor monitor) {
		LinkedList<Feature> selectedFeatures2 = new LinkedList<Feature>();
		selectedFeatures2.add(root);
		build(root, "", selectedFeatures2, monitor);
	}

	private void build(Feature currentFeature, String selected, LinkedList<Feature> selectedFeatures2, IProgressMonitor monitor) {
		if (monitor.isCanceled() || (configurationNumber != 0 && confs > configurationNumber)) {
			return;
		}
		if (selectedFeatures2.isEmpty()) {
			if (reader.readFromString(selected.toString())) {
				if (configuration.valid()) {
					LinkedList<String> selectedFeatures3 = new LinkedList<String>();
					for (String f : selected.split("[ ]")) {
						if (!f.equals("")) {
							selectedFeatures3.add(f);
						}
					}
					for (Feature f : configuration.getSelectedFeatures()) {
						if (f.isLayer()) {
							if (!selectedFeatures3.contains(f.getName())) {
								return;
							}
						}
					}
					for (String f : selectedFeatures3) {
						if (configuration.getSelectablefeature(f).getSelection() != Selection.SELECTED) {
							return;
						}
					}
					
					if (confs < 10) {
						zeros = "000";
					} else if (confs < 100) {
						zeros = "00";
					} else if (confs < 1000) {
						zeros = "0";
					} else {
						zeros = "";
					}
					monitor.subTask(SUBTASK_BUILD + confs + "/" + (configurationNumber == 0 ? "counting..." : configurationNumber));
					// TODO @Jens composer problem marker.
					// TODO @Jens compiler could be used to find and propagate errors.
					project.getComposer().buildConfiguration(folder.getFolder(CONFIGURATION_NAME + zeros + confs), configuration);
					confs++;
					if (confs <= configurationNumber || configurationNumber == 0) { 
						monitor.subTask(SUBTASK_GET + confs + "/" + (configurationNumber == 0 ? "counting..." : configurationNumber));
					}
					if (counting && configurationNumber != 0) {
						counting = false;
						monitor.beginTask("" , configurationNumber);
						monitor.worked((int)confs);
					}
					if (configurationNumber != 0) {
						monitor.worked(1);
					}
					
				}
			}
			return;
		}
		
		if (currentFeature.isAnd()) {
			buildAnd(selected, selectedFeatures2, monitor);
		} else if (currentFeature.isOr()) {
			buildOr(selected, selectedFeatures2, monitor);
		} else if (currentFeature.isAlternative()) {
			buildAlternative(selected, selectedFeatures2, monitor);
		}				
	}

	private void buildAlternative(String selected, LinkedList<Feature> selectedFeatures2, IProgressMonitor monitor) {
		Feature currentFeature = selectedFeatures2.getFirst();
		selectedFeatures2.removeFirst();
		LinkedList<Feature> selectedFeatures3 = new LinkedList<Feature>();
		if (currentFeature.isLayer()) {
			if (selected.equals("")) {
				selected = currentFeature.getName();
			} else {
				selected += " " + currentFeature.getName();
			}
		}
		if (!currentFeature.hasChildren()) {
			if (selectedFeatures2.isEmpty()) {
				currentFeature = null;
			} else {
				currentFeature = selectedFeatures2.getFirst();
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(currentFeature, selected, selectedFeatures3, monitor);
			return;
		}
		for (int i2 = 0;i2 < getChildren(currentFeature).size();i2++) {
			selectedFeatures3 = new LinkedList<Feature>();
			selectedFeatures3.add(getChildren(currentFeature).get(i2));
			selectedFeatures3.addAll(selectedFeatures2);
			build(selectedFeatures3.isEmpty() ? null : selectedFeatures3.getFirst(), selected, selectedFeatures3, monitor);
		}
	}


	private void buildOr(String selected, LinkedList<Feature> selectedFeatures2, IProgressMonitor monitor) {
		Feature currentFeature = selectedFeatures2.getFirst();
		selectedFeatures2.removeFirst();
		LinkedList<Feature> selectedFeatures3 = new LinkedList<Feature>();
		if (currentFeature.isLayer()) {
			if (selected.equals("")) {
				selected = currentFeature.getName();
			} else {
				selected += " " + currentFeature.getName();
			}
		}
		if (!currentFeature.hasChildren()) {
			if (selectedFeatures2.isEmpty()) {
				currentFeature = null;
			} else {
				currentFeature = selectedFeatures2.getFirst();
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(currentFeature, selected, selectedFeatures3, monitor);
			return;
		}
		int k2;
		int i2 = 1;
		if (getChildren(currentFeature).size() < currentFeature.getChildren().size()) {
			i2 = 0;
		}
		for (;i2 < (int)java.lang.Math.pow(2, getChildren(currentFeature).size());i2++) {
			k2 = i2;
			selectedFeatures3 = new LinkedList<Feature>();
			for (int j = 0;j < getChildren(currentFeature).size();j++) {
				if (k2%2 != 0) {
					selectedFeatures3.add(getChildren(currentFeature).get(j));
				}
				k2 = k2/2;
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(selectedFeatures3.isEmpty() ? null : selectedFeatures3.getFirst(), selected, selectedFeatures3, monitor);
		}
	}

	private void buildAnd(String selected, LinkedList<Feature> selectedFeatures2, IProgressMonitor monitor) {
		Feature currentFeature = selectedFeatures2.getFirst();
		selectedFeatures2.removeFirst();
		LinkedList<Feature> selectedFeatures3 = new LinkedList<Feature>();
		if (currentFeature.isLayer()) {
			if (selected.equals("")) {
				selected = currentFeature.getName();
			} else {
				selected += " " + currentFeature.getName();
			}
		}
		if (!currentFeature.hasChildren()) {
			if (selectedFeatures2.isEmpty()) {
				currentFeature = null;
			} else {
				currentFeature = selectedFeatures2.getFirst();
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(currentFeature, selected, selectedFeatures3, monitor);
			return;
		}
		int k2;
		LinkedList<Feature> optionalFeatures = new LinkedList<Feature>();
		for (Feature f : getChildren(currentFeature)) {
			if (f.isMandatory()) {
				selectedFeatures2.add(f);
			} else {
				optionalFeatures.add(f);
			}
		}
		for (int i2 = 0;i2 < (int)java.lang.Math.pow(2, optionalFeatures.size());i2++) {
			k2 = i2;
			selectedFeatures3 = new LinkedList<Feature>();
			for (int j = 0;j < optionalFeatures.size();j++) {
				if (k2%2 != 0) {
					selectedFeatures3.add(optionalFeatures.get(j));
				}
				k2 = k2/2;
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(selectedFeatures3.isEmpty() ? null : selectedFeatures3.getFirst(), selected, selectedFeatures3, monitor);
		}
		
	}

	private LinkedList<Feature> getChildren(Feature currentFeature) {
		LinkedList<Feature> children = new LinkedList<Feature>();
		for (Feature child : currentFeature.getChildren()) {
			if (child.isLayer() || hasLayerChild(child)) {
				children.add(child);
			}
		}
		return children;
	}

	private boolean hasLayerChild(Feature feature) {
		if (feature.hasChildren()) {
			for (Feature child : feature.getChildren()) {
				if (child.isLayer() || hasLayerChild(child)) {
					return true;
				}
			}
		}
		return false;
	}
}
