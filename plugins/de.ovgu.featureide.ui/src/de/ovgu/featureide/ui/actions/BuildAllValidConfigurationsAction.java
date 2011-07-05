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
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.core.CorePlugin;
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
public class BuildAllValidConfigurationsAction implements IObjectActionDelegate {
	
	private final static String FOLDER_NAME = "products"; 
	
	private final static String MESSAGE_TITLE = "Build all valid configurations";
	private final static String MESSAGE_START = "This could take a very long time.\n";
	private final static String MESSAGE_WARNING = "There are more than 31 features, this could cause some errors.\n";
	private final static String MESSAGE_END = "All products will be build into: \"";
	
	private final static String SUBTASK = "Check Configuration ";
	
	private final static String CONFIGURATION_NAME = "Variant";
	
	private ISelection selection;
	private IFeatureProject featureProject;
	
	public BuildAllValidConfigurationsAction() {
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
	@Override
	public void run(IAction action) {
		Object obj = ((IStructuredSelection)selection).getFirstElement();
		if (obj instanceof IResource) {
			IResource res = (IResource) obj;
			featureProject = CorePlugin.getFeatureProject(res);
			if (featureProject == null) {
				return;
			}
		} else {
			return;
		}
		if (openDialog()) {
			return;
		}

		Job job = new Job(MESSAGE_TITLE) {
			private IFeatureProject project;
			private IFolder folder;
			private FeatureModel featureModel;
			private long i;
			private LinkedList<String> layer;
			private Configuration configuration;
			private ConfigurationReader reader;
			private LinkedList<String> selectedFeatures;
			private StringBuffer text;
			private long confs;
			private long k;
			private String zeros;
			
			public IStatus run(IProgressMonitor monitor) {
				long time = System.currentTimeMillis();
				project = featureProject;
				featureModel = project.getFeatureModel();
				int j = (int)java.lang.Math.pow(2, (featureModel.getLayerNames().size()));
				monitor.beginTask("" , j);
				init(monitor);
				
				while(!monitor.isCanceled() && i < j) {
					monitor.subTask(SUBTASK + i + "/" + j);
						buildNext();
					i++;
					monitor.worked(1);
				}
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
				UIPlugin.getDefault().logInfo(confs + " configurations built in " + t);
				monitor.done();
				return Status.OK_STATUS;
			}
			
			
			private void init(IProgressMonitor monitor) {
				i = 0;
				confs = 0;
				folder = project.getProject().getFolder(FOLDER_NAME);
				selectedFeatures = new LinkedList<String>();
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
			
			/**
			 * TODO #280 This method needs some improvements.
			 * Converts a binary value into a configuration.
			 */
			private void buildNext() {
				selectedFeatures.clear();
				k = i;
				for (int j = 0;j < layer.size();j++) {
					if (k%2 != 0) {
						selectedFeatures.add(layer.get(j));
					}
					k = k/2;
				}
				
				text = new StringBuffer();
				for (String layer : selectedFeatures) {
					text.append(layer + " ");
				}
				if (reader.readFromString(text.toString())) {
					if (configuration.valid()) {
						for (Feature f : configuration.getSelectedFeatures()) {
							if (f.isLayer()) {
								if (!selectedFeatures.contains(f.getName())) {
									return;
								}
							}
						}
						for (String f : selectedFeatures) {
							if (configuration.getSelectablefeature(f).getSelection() != Selection.SELECTED) {
								return;
							}
						}
						confs++;
						if (confs < 10) {
							zeros = "000";
						} else if (confs < 100) {
							zeros = "00";
						} else if (confs < 1000) {
							zeros = "0";
						} else {
							zeros = "";
						}
						project.getComposer().buildConfiguration(folder.getFolder(CONFIGURATION_NAME + zeros + confs), configuration);
					}
				}
			}

		};
		job.setPriority(Job.BUILD);
		job.schedule();
	}

	private boolean openDialog() {
		String message = MESSAGE_START;
		if (featureProject.getFeatureModel().getLayers().size() > 31) {
			message += MESSAGE_WARNING;
		}
		message += MESSAGE_END +
			featureProject.getProject().getFolder(FOLDER_NAME).getFullPath().toOSString() + "\"";
		return !MessageDialog.openConfirm(null, MESSAGE_TITLE, message);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
	 */
	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection; 
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(org.eclipse.jface.action.IAction, org.eclipse.ui.IWorkbenchPart)
	 */
	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {

	}

}
