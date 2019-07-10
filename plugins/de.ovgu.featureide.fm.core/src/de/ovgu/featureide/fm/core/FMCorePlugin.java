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
package de.ovgu.featureide.fm.core;

import java.util.List;

import javax.annotation.CheckForNull;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.init.FMCoreEclipseLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.util.JobSequence;

/**
 * The activator class controls the plug-in life cycle.
 *
 * @author Thomas Thuem
 */
public class FMCorePlugin extends AbstractCorePlugin {

	private static FMCorePlugin plugin;

	@Override
	public String getID() {
		return PluginID.PLUGIN_ID;
	}

	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		LibraryManager.registerLibrary(new FMCoreEclipseLibrary());
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		LibraryManager.deregisterLibraries();
		plugin = null;
		super.stop(context);
	}

	public static FMCorePlugin getDefault() {
		return plugin;
	}

	@CheckForNull
	public static IFolder createFolder(IProject project, String name) {
		final IFolder folder = getFolder(project, name);
		if ((folder != null) && !folder.exists()) {
			try {
				folder.create(false, true, null);
			} catch (final CoreException e) {
				FMCorePlugin.getDefault().logError(e);
			}
		}
		return folder;
	}

	@CheckForNull
	public static IFolder getFolder(IProject project, String name) {
		IFolder folder = null;
		if ((name != null) && !name.trim().isEmpty()) {
			for (final String folderName : name.split("[/]")) {
				folder = (folder == null) ? project.getFolder(folderName) : folder.getFolder(folderName);
			}
		}
		return folder;
	}

	/**
	 * Creates a {@link LongRunningMethod} for every project with the given arguments.
	 *
	 * @param projects the list of projects
	 * @param arguments the arguments for the job
	 * @param autostart if {@code true} the jobs is started automatically.
	 * @return the created job or a {@link JobSequence} if more than one project is given. Returns {@code null} if {@code projects} is empty.
	 */
	public static LongRunningMethod<?> startJobs(List<LongRunningMethod<?>> projects, String jobName, boolean autostart) {
		LongRunningMethod<?> ret;
		switch (projects.size()) {
		case 0:
			return null;
		case 1:
			ret = projects.get(0);
			break;
		default:
			final JobSequence jobSequence = new JobSequence();
			jobSequence.setIgnorePreviousJobFail(true);
			for (final LongRunningMethod<?> p : projects) {
				jobSequence.addJob(p);
			}
			ret = jobSequence;
		}
		if (autostart) {
			LongRunningWrapper.getRunner(ret, jobName).schedule();
		}
		return ret;
	}

}
