/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.mpl.builder;

import static de.ovgu.featureide.fm.core.localization.StringTable.NO_PROJECT_GOT;

import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.job.MPLBuildProjectJob;
import de.ovgu.featureide.core.mpl.job.MPLRenameExternalJob;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.core.job.util.JobSequence;

/**
 * A simple multi product line builder.
 *
 * @author Sebastian Krieter
 */
public class MSPLBuilder extends IncrementalProjectBuilder {

	public static final String BUILDER_ID = MPLPlugin.PLUGIN_ID + ".MSPLBuilder";
	public static final String COMPOSER_KEY = "composer";

	public MSPLBuilder() {
		super();
	}

	@Override
	protected void clean(IProgressMonitor monitor) throws CoreException {
		// TODO: prevent automatic build
//		IProject project = getProject();
//		if (project != null) {
//			cleanProject(CorePlugin.getFeatureProject(project), monitor);
//		} else {
//			MPLPlugin.getDefault().logWarning(NO_PROJECT_GOT);
//		}
	}

//	private boolean cleanProject(IFeatureProject featureProject, IProgressMonitor monitor) {
//		final IFolder buildFolder = featureProject.getBuildFolder();
//		try {
//			for (IResource member : buildFolder.members()) {
//				member.delete(true, monitor);
//			}
//		} catch (CoreException e) {
//			MPLPlugin.getDefault().logError(e);
//			return false;
//		}
//		return true;
//	}

	private final HashMap<String, Boolean> buildMap = new HashMap<String, Boolean>();

	@SuppressWarnings({ "rawtypes", "unchecked" })
	@Override
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor) {
		final IProject project = getProject();
		if (project != null) {
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
			if ((featureProject == null) || !featureProject.buildRelevantChanges()) {
				return null;
			}

			Boolean building;
			synchronized (buildMap) {
				building = buildMap.get(project.getName());
				if (building == null) {
					building = false;
				}
				if (building) {
					return null;
				} else {
					buildMap.put(project.getName(), true);
				}
			}

			try {
				final Configuration config = new Configuration(featureProject.getFeatureModel());

				final IFile configFile = featureProject.getCurrentConfiguration();
				SimpleFileHandler.load(Paths.get(configFile.getLocationURI()), config, ConfigFormatManager.getInstance());

				// build
				final IFolder buildFolder = featureProject.getBuildFolder();
				final LongRunningMethod<?> job = new MPLBuildProjectJob.Arguments(featureProject, featureProject, buildFolder, config, null).createJob();

				final String tempConfigName = featureProject.getCurrentConfiguration().getName();
				final String configName;
				final int splitIndex = tempConfigName.lastIndexOf('.');
				if (splitIndex > -1) {
					configName = tempConfigName.substring(0, splitIndex);
				} else {
					configName = tempConfigName;
				}

				final JobSequence buildSequence = new JobSequence();
				buildSequence.setIgnorePreviousJobFail(false);
				buildSequence.addJob(job);
				final IRunner<Boolean> runner = LongRunningWrapper.getRunner(buildSequence);
				runner.addJobFinishedListener(new JobFinishListener() {

					@Override
					public void jobFinished(IJob finishedJob) {
						MPLRenameExternalJob.setJavaBuildPath(project, buildFolder.getFolder(configName).getFullPath());
						synchronized (buildMap) {
							buildMap.put(project.getName(), false);
						}
						featureProject.built();
					}
				});
				runner.schedule();
			} catch (final Exception e) {
				MPLPlugin.getDefault().logError(e);
				synchronized (buildMap) {
					buildMap.put(project.getName(), false);
				}
			}
		} else {
			MPLPlugin.getDefault().logWarning(NO_PROJECT_GOT);
		}
		return null;
	}
}
