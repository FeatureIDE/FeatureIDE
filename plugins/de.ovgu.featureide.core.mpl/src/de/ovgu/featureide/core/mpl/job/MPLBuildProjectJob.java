/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.mpl.job;

import static de.ovgu.featureide.fm.core.localization.StringTable.BUILT_MPL_PROJECT_;
import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY___;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_MAPPING_FILE_SPECIFIED_;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.builder.MSPLNature;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagator;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobSequence;

/**
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public class MPLBuildProjectJob implements LongRunningMethod<Boolean> {

	private final IFeatureProject externalFeatureProject;
	private final IFeatureProject rootFeatureProject;
	private final Configuration configuration;
	private final String varName;
	private final IFolder buildF;

	public MPLBuildProjectJob(IFeatureProject rootFeatureProject, IFeatureProject externalFeatureProject, IFolder buildFolder, Configuration configuration,
			String varName) {
		this.rootFeatureProject = rootFeatureProject;
		this.externalFeatureProject = externalFeatureProject;
		buildF = buildFolder;
		this.configuration = configuration;
		this.varName = varName;
	}

	IFolder internTempBuildFolder = null;
	IFolder rootBuildFolder = null;

	@Override
	public Boolean execute(IMonitor<Boolean> workMonitor) throws Exception {
		try {
			if (externalFeatureProject.getProject().hasNature(MSPLNature.NATURE_ID)) {
				if (!buildMPLProject()) {
					return false;
				}
			} else {
				if (!buildFeatureProject(varName, buildF)) {
					return false;
				}
			}
		} catch (final CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		MPLPlugin.getDefault().logInfo(BUILT_MPL_PROJECT_);
		return true;
	}

	private void buildExternalProject(String projectName, Configuration config, String configName) {

		final JobSequence curJobSequence = JobSequence.getSequenceForJob(this);
		if (curJobSequence != null) {
			final IProject externalProject = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
			final IFeatureProject externalFeatureProject = CorePlugin.getFeatureProject(externalProject);

			final ArrayList<LongRunningMethod<?>> jobList = new ArrayList<>(3);

			// build
			jobList.add(new MPLBuildProjectJob(rootFeatureProject, externalFeatureProject, internTempBuildFolder, config, configName));

			// rename
			jobList.add(new MPLRenameExternalJob(externalFeatureProject.getProject(), configName, internTempBuildFolder.getFullPath()));

			// copy
			jobList.add(new MPLCopyExternalJob(internTempBuildFolder, rootBuildFolder));

			curJobSequence.insertJobs(this, jobList);
		}

	}

	private boolean buildMPLProject() {
		final IFeatureModel featureModel = externalFeatureProject.getFeatureModel();
		if (!(featureModel instanceof MultiFeatureModel)) {
			return false;
		}

		if (varName == null) {
			final String varName = FileHandler.getFileName(externalFeatureProject.getCurrentConfiguration());
			rootBuildFolder = buildF.getFolder(varName);
			internTempBuildFolder = buildF.getFolder(EMPTY___ + varName);
		} else {
			rootBuildFolder = buildF;
			internTempBuildFolder = externalFeatureProject.getBuildFolder();
		}

		try {
			if (!rootBuildFolder.exists()) {
				rootBuildFolder.create(true, true, null);
			}
		} catch (final CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		// build own project
		// featureProject.deleteBuilderMarkers(featureProject.getProject(),
		// IResource.DEPTH_INFINITE);
		if (!buildFeatureProject(varName, rootBuildFolder)) {
			return false;
		}

		try {
			if (internTempBuildFolder.exists()) {
				internTempBuildFolder.delete(true, null);
			}
			internTempBuildFolder.create(true, true, null);
		} catch (final CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		// get mapping of other projects
		final MultiFeatureModel extFeatureModel = (MultiFeatureModel) featureModel;
		final Configuration mappedProjects = new Configuration(new FeatureModelFormula(extFeatureModel.getMappingModel()));
		try {
			String mappingFileName = externalFeatureProject.getProject().getPersistentProperty(MPLPlugin.mappingConfigID);
			// XXX MPL save information in builder not as persistent property
			if (mappingFileName == null) {
				mappingFileName = "default.xml";
				externalFeatureProject.getProject().setPersistentProperty(MPLPlugin.mappingConfigID, mappingFileName);
			}
			final IFile mappingFile = externalFeatureProject.getProject().getFile("InterfaceMapping/" + mappingFileName);
			if (mappingFile == null) {
				MPLPlugin.getDefault().logInfo(NO_MAPPING_FILE_SPECIFIED_);
				return false;
			}
			final IFile configFile = externalFeatureProject.getProject().getFile("InterfaceMapping/" + mappingFileName);
			SimpleFileHandler.load(EclipseFileSystem.getPath(configFile), mappedProjects, ConfigFormatManager.getInstance());
		} catch (final Exception e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		// build other projects
		// build interfaces
		for (final IFeature mappedProject : mappedProjects.getSelectedFeatures()) {
			if (mappedProject.getStructure().isConcrete()) {
				final int splittIndex = mappedProject.getName().lastIndexOf('.');
				if (splittIndex == -1) {
					// can this happen???
					continue;
				}
				final String projectName = mappedProject.getName().substring(splittIndex + 1);
				final String configName = mappedProject.getName().substring(0, splittIndex);

				buildExternalProject(projectName, configuration, configName);
			}
		}

		// build instances
		for (final UsedModel usedModel : extFeatureModel.getExternalModels().values()) {
			if (usedModel.getType() == MultiFeature.TYPE_INSTANCE) {
				final String projectName = usedModel.getModelName();
				final String configName = usedModel.getVarName();

				buildExternalProject(projectName, configuration, configName);
			}
		}

		return true;
	}

	private boolean buildFeatureProject(String varName, IFolder buildFolder) {
		final IComposerExtensionClass composerExtension = externalFeatureProject.getComposer();
		if (composerExtension == null) {
			return false;
		}

		// Refresh model and
		// Delete all files in the build folder
		try {
			externalFeatureProject.getProject().refreshLocal(IResource.DEPTH_ONE, null);
			for (final IResource member : buildFolder.members()) {
				member.delete(true, null);
			}
			buildFolder.refreshLocal(IResource.DEPTH_ZERO, null);
		} catch (final CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		if (varName != null) {
			// Get partial configs
			// TODO MPL: config for other MPL projects may not working
			final IFeatureModel fm = rootFeatureProject.getFeatureModel();
			if (fm instanceof MultiFeatureModel) {
				final MultiFeatureModel efm = (MultiFeatureModel) fm;
				final UsedModel usedModel = efm.getExternalModel(varName);
				final String prefix = usedModel.getPrefix() + ".";

				final FeatureModelFormula snapshot = externalFeatureProject.getFeatureModelManager().getPersistentFormula();
				final Configuration newConfiguration = new Configuration(snapshot);
				final ConfigurationPropagator propagator = new ConfigurationPropagator(snapshot, newConfiguration);

				for (final SelectableFeature feature : configuration.getFeatures()) {
					if (feature.getName().startsWith(prefix)) {
						final String featureName = feature.getName().substring(prefix.length());
						newConfiguration.setManual(featureName, feature.getSelection());
					}
				}

				// Find Random Solution
				LongRunningWrapper.runMethod(propagator.completeRandomly());

				// Build project
				composerExtension.buildConfiguration(buildFolder, newConfiguration, varName);
			}
		} else {
			// Build project
			composerExtension.buildConfiguration(buildFolder, configuration, FileHandler.getFileName(externalFeatureProject.getCurrentConfiguration()));
		}

		try {
			buildFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (final CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		return true;
	}

}
