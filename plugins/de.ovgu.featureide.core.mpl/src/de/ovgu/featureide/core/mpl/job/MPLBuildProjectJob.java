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
package de.ovgu.featureide.core.mpl.job;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.builder.MSPLNature;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.job.util.IChainJob;
import de.ovgu.featureide.fm.core.ExtendedFeature;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;

/**
 * 
 * @author Sebastian Krieter
 */
public class MPLBuildProjectJob extends AMonitorJob<MPLBuildProjectJob.Arguments> {

	public static class Arguments extends AJobArguments {
		private final IFeatureProject externalFeatureProject;
		private final IFeatureProject rootFeatureProject;
		private final Configuration configuration;
		private final String varName;
		private final IFolder buildF;
		
		public Arguments(IFeatureProject rootFeatureProject, IFeatureProject externalFeatureProject, IFolder buildFolder, Configuration configuration, String varName) {
			super(Arguments.class);
			this.rootFeatureProject = rootFeatureProject;
			this.externalFeatureProject = externalFeatureProject;
			this.buildF = buildFolder;
			this.configuration = configuration;
			this.varName = varName;
		}
	}

	protected MPLBuildProjectJob(Arguments arguments) {
		super("Build External Project", arguments);
		setPriority(BUILD);
	}
	
	IFolder internTempBuildFolder = null;
	IFolder rootBuildFolder = null;

	@Override
	protected boolean work() {
		try {
			if(arguments.externalFeatureProject.getProject().hasNature(MSPLNature.NATURE_ID)) {
				if (!buildMPLProject()) {
					return false;
				}
			} else {
				if (!buildFeatureProject(arguments.varName, arguments.buildF)) {
					return false;
				}
			}
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		MPLPlugin.getDefault().logInfo("Built MPL Project.");
		return true;
	}
	
	private void buildExternalProject(String projectName, Configuration config, String configName) {
		final IProject externalProject = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
		final IFeatureProject externalFeatureProject = CorePlugin.getFeatureProject(externalProject);
		
		final ArrayList<IChainJob> jobList = new ArrayList<IChainJob>(3);
		
		//build
		jobList.add(createJob(new MPLBuildProjectJob.Arguments(arguments.rootFeatureProject,
				externalFeatureProject, internTempBuildFolder, config, configName)));
		
		// rename
		jobList.add(createJob(new MPLRenameExternalJob.Arguments(
				arguments.externalFeatureProject.getProject(), configName, 
				internTempBuildFolder.getFullPath())));
		
		// copy
		jobList.add(createJob(new MPLCopyExternalJob.Arguments(
				internTempBuildFolder, rootBuildFolder)));
		
		JobManager.insertJobs(this, jobList);
	}
	
	private IChainJob createJob(AJobArguments arg) {
		IChainJob curJob = arg.createJob();
		curJob.setIgnorePreviousJobFail(false);
		return curJob;
	}
	
	private boolean buildMPLProject() {
		final FeatureModel featureModel = arguments.externalFeatureProject.getFeatureModel();
		if (!(featureModel instanceof ExtendedFeatureModel)) {
			return false;
		}
		
		if (arguments.varName == null) {
			String varName = arguments.externalFeatureProject.getCurrentConfiguration().getName();
			final int splitIndex = varName.lastIndexOf('.');
			if (splitIndex > -1) {
				varName = varName.substring(0, splitIndex);
			}
			rootBuildFolder = arguments.buildF.getFolder(varName);
			internTempBuildFolder = arguments.buildF.getFolder("_" + varName);
		} else {
			rootBuildFolder = arguments.buildF;
			internTempBuildFolder = arguments.externalFeatureProject.getBuildFolder();
		}
		
		try {
			if (!rootBuildFolder.exists()) {
				rootBuildFolder.create(true, true, monitor);
			}
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		
		// build own project
		// featureProject.deleteBuilderMarkers(featureProject.getProject(), IResource.DEPTH_INFINITE);
		if (!buildFeatureProject(arguments.varName, rootBuildFolder)) {
			return false;
		}
				
		try {
			if (internTempBuildFolder.exists()) {
				internTempBuildFolder.delete(true, monitor);
			}
			internTempBuildFolder.create(true, true, monitor);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		
		// get mapping of other projects
		final ExtendedFeatureModel extFeatureModel = (ExtendedFeatureModel) featureModel;
		final Configuration mappedProjects = new Configuration(extFeatureModel.getMappingModel());
		try {
			String mappingFileName = arguments.externalFeatureProject.getProject().getPersistentProperty(MPLPlugin.mappingConfigID);
			// XXX MPL save information in builder not as persistent property
			if (mappingFileName == null) {
				mappingFileName = "default.config";
				arguments.externalFeatureProject.getProject().setPersistentProperty(MPLPlugin.mappingConfigID, mappingFileName);
			}
			IFile mappingFile = arguments.externalFeatureProject.getProject().getFile("InterfaceMapping/" + mappingFileName);
			if (mappingFile == null) {
				MPLPlugin.getDefault().logInfo("No mapping file specified.");
				return false;
			}
			new ConfigurationReader(mappedProjects).readFromFile(arguments.externalFeatureProject.getProject().getFile("InterfaceMapping/" + mappingFileName));
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		
		// build other projects
		// build interfaces
		for (final Feature mappedProject : mappedProjects.getSelectedFeatures()) {
			if (mappedProject.isConcrete()) {
				final int splittIndex = mappedProject.getName().lastIndexOf('.');
				if (splittIndex == -1) {
					// can this happen???
					continue;
				}
				final String projectName = mappedProject.getName().substring(splittIndex + 1);
				final String configName = mappedProject.getName().substring(0, splittIndex);
				
				buildExternalProject(projectName, arguments.configuration, configName);
			}
		}
		
		// build instances
		for (UsedModel usedModel : extFeatureModel.getExternalModels().values()) {
			if (usedModel.getType() == ExtendedFeature.TYPE_INSTANCE) {
				final String projectName = usedModel.getModelName();
				final String configName = usedModel.getVarName();
				
				buildExternalProject(projectName, arguments.configuration, configName);
			}
		}
		
		return true;
	}
	
	private boolean buildFeatureProject(String varName, IFolder buildFolder) {
		final IComposerExtensionClass composerExtension = arguments.externalFeatureProject.getComposer();
		if (composerExtension == null) {
			return false;
		}

		// Refresh model and
		// Delete all files in the build folder
		try {
			arguments.externalFeatureProject.getProject().refreshLocal(IResource.DEPTH_ONE, null);
			for (IResource member : buildFolder.members()) {
				member.delete(true, monitor);
			}
			buildFolder.refreshLocal(IResource.DEPTH_ZERO, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		
		if (varName != null) {
			// Get partial configs 
			// TODO MPL: config for other MPL projects may not working
			FeatureModel fm = arguments.rootFeatureProject.getFeatureModel();
			if (fm instanceof ExtendedFeatureModel) {
				ExtendedFeatureModel efm = (ExtendedFeatureModel) fm;
				UsedModel usedModel = efm.getExternalModel(varName);
				String prefix = usedModel.getPrefix() + ".";
				
				final Configuration newConfiguration = new Configuration(arguments.externalFeatureProject.getFeatureModel());				
				
				for (SelectableFeature feature : arguments.configuration.getFeatures()) {
					if (feature.getName().startsWith(prefix)) {
						String featureName = feature.getName().substring(prefix.length());
						try {
							newConfiguration.setManual(featureName, feature.getSelection());
						} catch (Exception e) {
						}
					}
				}
				
				// Find Random Solution
				try {
					LinkedList<List<String>> solutions = newConfiguration.getSolutions(1);
					if (!solutions.isEmpty()) {
						newConfiguration.resetValues();
						List<String> solution = solutions.getFirst();
						for (String solutionFeatureName : solution) {
							try {
								newConfiguration.setManual(solutionFeatureName, Selection.SELECTED);
							} catch (Exception e) {
							}
						}
					}
				} catch (TimeoutException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}
				
				// Build project
				composerExtension.buildConfiguration(buildFolder, newConfiguration, varName);
			}			
		} else {
			// Build project
			String configName = arguments.externalFeatureProject.getCurrentConfiguration().getName();
			final int splitIndex = configName.lastIndexOf('.');
			if (splitIndex > -1) {
				configName = configName.substring(0, splitIndex);
			}
			
			composerExtension.buildConfiguration(buildFolder, arguments.configuration, configName);
		}
		
		try {
			buildFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		
		return true;
	}
}
