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

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtension;
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
		private final Configuration configuration;
		private final String varName;
		private final IFolder buildF;
		
		public Arguments(IFeatureProject externalFeatureProject, IFolder buildFolder, Configuration configuration, String varName) {
			super(Arguments.class);
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
				if (!buildMPLProject(arguments.externalFeatureProject, arguments.configuration, arguments.varName)) {
					return false;
				}
			} else {
				if (!buildFeatureProject(arguments.externalFeatureProject, arguments.configuration, arguments.varName, arguments.buildF)) {
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
		jobList.add(createJob(new MPLBuildProjectJob.Arguments(
				externalFeatureProject, internTempBuildFolder, config, configName)));
		
		// rename
		jobList.add(createJob(new MPLRenameExternalJob.Arguments(
				arguments.externalFeatureProject.getProject(), configName, 
				internTempBuildFolder.getFullPath()
//				externalFeatureProject.getBuildFolder().getFolder(configName).getFullPath()
				)));
		
		// copy
		jobList.add(createJob(new MPLCopyExternalJob.Arguments(
				internTempBuildFolder
//				externalFeatureProject.getBuildFolder().getFolder(configName)
				, rootBuildFolder
//				tempBuildFolder
				)));
		
		JobManager.insertJobs(this, jobList);
	}
	
	private IChainJob createJob(AJobArguments arg) {
		IChainJob curJob = arg.createJob();
		curJob.setIgnorePreviousJobFail(false);
		return curJob;
	}
	
	private boolean buildMPLProject(IFeatureProject mplFeatureProject, Configuration config, String varName) {
		final FeatureModel featureModel = mplFeatureProject.getFeatureModel();
		if (!(featureModel instanceof ExtendedFeatureModel)) {
			return false;
		}
		
		if (varName == null) {
			varName = mplFeatureProject.getCurrentConfiguration().getName();
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

//		final IFolder tempBuildFolder = arguments.buildF.getFolder(varName);
//		tempExternBuildFolder = arguments.buildF.getFolder("_" + varName);
		try {
			if (internTempBuildFolder.exists()) {
				internTempBuildFolder.delete(true, monitor);
			}
			if (!rootBuildFolder.exists()) {
				rootBuildFolder.create(true, true, null);
			}
			internTempBuildFolder.create(true, true, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		
		// build own project
		// featureProject.deleteBuilderMarkers(featureProject.getProject(), IResource.DEPTH_INFINITE);
		if (!buildFeatureProject(mplFeatureProject, config, varName, rootBuildFolder)) {
			return false;
		}

		// get mapping of other projects
		final ExtendedFeatureModel extFeatureModel = (ExtendedFeatureModel) featureModel;
		final Configuration mappedProjects = new Configuration(extFeatureModel.getMappingModel());
		try {
			String mappingFileName = mplFeatureProject.getProject().getPersistentProperty(MPLPlugin.mappingConfigID);
			if (mappingFileName == null) {
				MPLPlugin.getDefault().logInfo("No mapping file specified.");
				return false;
			}
			new ConfigurationReader(mappedProjects).readFromFile(mplFeatureProject.getProject().getFile("InterfaceMapping/" + mappingFileName));
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
				
				buildExternalProject(projectName, config, configName);
			}
		}
		
		// build instances
		for (UsedModel usedModel : extFeatureModel.getExternalModels().values()) {
			if (usedModel.getType() == ExtendedFeature.TYPE_INSTANCE) {
				final String projectName = usedModel.getModelName();
				final String configName = usedModel.getVarName();
				
				buildExternalProject(projectName, config, configName);
			}
		}
		
		return true;
	}
	
	private boolean buildFeatureProject(IFeatureProject featureProject, Configuration config, String varName, IFolder buildFolder) {
		final IComposerExtension composerExtension = featureProject.getComposer();
		if (composerExtension == null) {
			return false;
		}

		// Refresh model
		try {
			featureProject.getProject().refreshLocal(IResource.DEPTH_ONE, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
		}
		
		if (varName != null) {
			// Get partial configs 
			// TODO MPL: config richtig anpassen
			final Configuration newConfiguration = new Configuration(featureProject.getFeatureModel());
			for (SelectableFeature feature : config.getFeatures()) {
				if (feature.getName().startsWith(varName + ".")) {
					String featureName = feature.getName().substring(varName.length() + 1);
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
			
			// Delete all files in the build folder
//			final IFolder buildFolder = externalFeatureProject.getBuildFolder();
//			tempBuildFolder = featureProject.getBuildFolder().getFolder(varName);
//			final IFolder tempRenameFolder = tempBuildFolder.getFolder(varName);
			try {
//				if (tempBuildFolder.exists()) {
					for (IResource member : buildFolder.members()) {
						member.delete(true, monitor);
					}
//				} else {
//					tempBuildFolder.create(true, true, null);
//				}
				
//				tempRenameFolder.create(true, true, null);
			} catch (CoreException e) {
				MPLPlugin.getDefault().logError(e);
				return false;
			}
			
//			//TODO MPL: is this necessary
//			String configName = featureProject.getCurrentConfiguration().getName();
//			final int splitIndex = configName.lastIndexOf('.');
//			if (splitIndex > -1) {
//				configName = configName.substring(0, splitIndex);
//			}
			
			// Build project
			composerExtension.initialize(featureProject);
			composerExtension.buildConfiguration(buildFolder, newConfiguration, varName); //varName
//			buildPath = tempFolder1;
		} else {
			// Build project
			String configName = featureProject.getCurrentConfiguration().getName();
			final int splitIndex = configName.lastIndexOf('.');
			if (splitIndex > -1) {
				configName = configName.substring(0, splitIndex);
			}
			
			composerExtension.initialize(featureProject);
			composerExtension.buildConfiguration(buildFolder, config, configName);
		}
		
		return true;
	}
}