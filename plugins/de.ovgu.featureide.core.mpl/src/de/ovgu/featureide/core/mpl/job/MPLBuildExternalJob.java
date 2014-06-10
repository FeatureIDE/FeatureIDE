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

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.job.util.AMonitorJob;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.configuration.ConfigurationWriter;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;

/**
 * 
 * @author Sebastian Krieter
 */
public class MPLBuildExternalJob extends AMonitorJob<MPLBuildExternalJob.Arguments> {

	public static class Arguments extends AJobArguments {
		private final IFeatureProject externalFeatureProject;
		private final IFolder buildFolder;
		private final String configName;
		private final Configuration config;

		public Arguments(IFeatureProject externalProject, IFolder buildFolder, Configuration config,
				String configName) {
			super(Arguments.class);
			this.externalFeatureProject = externalProject;
			this.buildFolder = buildFolder;
			this.config = config;
			this.configName = configName;
		}
	}

	public MPLBuildExternalJob() {
		this(null);
	}

	protected MPLBuildExternalJob(Arguments arguments) {
		super("Build External Project", arguments);
		setPriority(BUILD);
	}

	private IFile tempConfigFile = null;

	@Override
	protected boolean work() {
		tempConfigFile = arguments.externalFeatureProject.getProject().getFile("tempConfig.config");

		if (!processFeatureProject(arguments.externalFeatureProject.getFeatureModel(), arguments.configName, arguments.config)) {
			return false;
		}
		
		IFolder buildFolder = arguments.buildFolder;
		try {
			for (IResource member : buildFolder.members()) {
				member.delete(true, monitor);
			}
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		IComposerExtension composerExtension = arguments.externalFeatureProject.getComposer();
		if (composerExtension != null) {
			composerExtension.initialize(arguments.externalFeatureProject);
			composerExtension.performFullBuild(tempConfigFile);

			Configuration c = new Configuration(arguments.externalFeatureProject.getFeatureModel());
			ConfigurationReader reader = new ConfigurationReader(c);
			try {
				reader.readFromFile(tempConfigFile);
			} catch (Exception e) {
				CorePlugin.getDefault().logError(e);
				return false;
			}
			composerExtension.copyNotComposedFiles(c, arguments.externalFeatureProject.getBuildFolder());
			
			IFolder tempFolder = buildFolder.getFolder(arguments.configName);
			if (!tempFolder.exists()) {
				try {
					tempFolder.create(true, true, null);
				} catch (CoreException e) {
					CorePlugin.getDefault().logError(e);
					return false;
				}
			}
			
			try {
				buildFolder.refreshLocal(IResource.DEPTH_INFINITE, monitor);
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}

		MPLPlugin.getDefault().logInfo("Built External Project.");
		return true;
	}

	private boolean processFeatureProject(FeatureModel featureModel, String configName, Configuration config) {
		// Get partial configs
		final Configuration newConfiguration = new Configuration(featureModel);
		for (SelectableFeature feature : config.getFeatures()) {
			if (feature.getName().startsWith(configName + ".")) {
				String featureName = feature.getName().substring(
						configName.length() + 1);
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

		// save config file
		try {
			new ConfigurationWriter(newConfiguration).saveToFile(tempConfigFile);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}
}
