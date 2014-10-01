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
package de.ovgu.featureide.core.mpl.builder;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.job.JobManager;
import de.ovgu.featureide.core.mpl.job.MPLBuildProjectJob;
import de.ovgu.featureide.core.mpl.job.MPLRenameExternalJob;
import de.ovgu.featureide.core.mpl.job.SequenceFinishedListener;
import de.ovgu.featureide.core.mpl.job.util.IChainJob;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;

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

	protected void clean(IProgressMonitor monitor) throws CoreException {
		// TODO: prevent automatic build
//		IProject project = getProject();
//		if (project != null) {
//			cleanProject(CorePlugin.getFeatureProject(project), monitor);
//		} else {
//			MPLPlugin.getDefault().logWarning("no project got");
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

	@SuppressWarnings("rawtypes")
	@Override
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor) {
		final IProject project = getProject();
		if (project != null) {
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
			if (featureProject == null || !featureProject.buildRelevantChanges()) {
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
				new ConfigurationReader(config).readFromFile(featureProject.getCurrentConfiguration());
				
				// build
				final Object buildObject = new Object();
				final IFolder buildFolder = featureProject.getBuildFolder();
				final IChainJob job = new MPLBuildProjectJob.Arguments(featureProject, featureProject, buildFolder, config, null).createJob();
				
				String tempConfigName = featureProject.getCurrentConfiguration().getName();
				final String configName;
				final int splitIndex = tempConfigName.lastIndexOf('.');
				if (splitIndex > -1) {
					configName = tempConfigName.substring(0, splitIndex);
				} else {
					configName = tempConfigName;
				}
				
				JobManager.addJob(buildObject, job, false);
				JobManager.addSequenceFinishedListener(buildObject, new SequenceFinishedListener() {
					@Override
					public void sequenceFinished(Object idObject, boolean success) {
						MPLRenameExternalJob.setJavaBuildPath(project, buildFolder.getFolder(configName).getFullPath());
						synchronized (buildMap) {
							buildMap.put(project.getName(), false);
						}
						featureProject.built();
					}
				});
				JobManager.startSequence(buildObject);
			} catch (Exception e) {
				MPLPlugin.getDefault().logError(e);
				synchronized (buildMap) {
					buildMap.put(project.getName(), false);
				}
			}
			
			
		} else {
			MPLPlugin.getDefault().logWarning("no project got");
		}
		return null;
	}
}