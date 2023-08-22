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

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.QualifiedName;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.init.FMCoreEclipseLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
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

	private static final QualifiedName MODEL_PATH = new QualifiedName("de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor#MODEL_PATH",
			"de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor#MODEL_PATH");

	@Override
	public String getID() {
		return PluginID.PLUGIN_ID;
	}

	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		LibraryManager.registerLibrary(FMCoreEclipseLibrary.getInstance());
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
	 * @param jobName the job's name
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

	public static Optional<IFile> findModelFile(IProject project) {
		final Optional<IPath> persitentModelFilePath = getPersitentModelFilePath(project);
		if ((persitentModelFilePath.isPresent()) && project.getFile(persitentModelFilePath.get()).exists()) {
			return persitentModelFilePath.map(project::getFile);
		} else if (isFeatureModel(project, "mpl.velvet")) {
			return getModelFile(project, "mpl.velvet");
		} else if (isFeatureModel(project, "model.uvl")) {
			return getModelFile(project, "model.uvl");
		} else if (isFeatureModel(project, "model.xml")) {
			return getModelFile(project, "model.xml");
		} else {
			final ArrayList<IFile> potentialModelFiles = findModelFiles(project);
			return potentialModelFiles.size() == 1 //
				? getModelFile(project, potentialModelFiles.get(0)) //
				: Optional.empty();
		}
	}

	/**
	 * @param project
	 * @return
	 */
	private static boolean isFeatureModel(IProject project, String fileName) {
		return FMCorePlugin.isFeatureModelFile(project.getFile(fileName));
	}

	private static Optional<IFile> getModelFile(IProject project, String fileName) {
		return getModelFile(project, project.getFile(fileName));
	}

	private static Optional<IFile> getModelFile(IProject project, IFile modelFile) {
		FMCorePlugin.setPersitentModelFilePath(project.getProject(), modelFile.getLocation().toOSString());
		return Optional.of(modelFile);
	}

	private static ArrayList<IFile> findModelFiles(IProject project) {
		final ArrayList<IFile> modelFiles = new ArrayList<>();
		try {
			project.accept(new IResourceVisitor() {

				@Override
				public boolean visit(IResource resource) throws CoreException {
					if (resource instanceof IFile) {
						if (resource.isAccessible()) {
							final IPersistentFormat<IFeatureModel> format =
								FMFormatManager.getInstance().getFormatByContent(EclipseFileSystem.getPath(resource));
							if (format != null) {
								modelFiles.add((IFile) resource);
							}
						}
					}
					return true;
				}
			}, IResource.DEPTH_ONE, true);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return modelFiles;
	}

	/**
	 * Saves the given path at persistent properties of the project
	 *
	 * @param path The path of the models file
	 * @param project
	 */
	public static void setPersitentModelFilePath(IProject project, String path) {
		try {
			project.setPersistentProperty(MODEL_PATH, Optional.ofNullable(path) //
					.map(Paths::get) //
					.filter(Files::exists) //
					.map(p -> p.isAbsolute() //
						? EclipseFileSystem.getResource(p) //
						: project.getFile(p.toString())) //
					.map(IResource::getLocation) //
					.map(IPath::toOSString) //
					.orElse(null));
		} catch (final Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the models path at persistent properties of the project
	 *
	 * @param project
	 * @return The saved path or {@code null} if there is none.
	 */
	public static Optional<IPath> getPersitentModelFilePath(IProject project) {
		try {
			return Optional.ofNullable(project.getPersistentProperty(MODEL_PATH)) //
					.map(Paths::get) //
					.map(p -> p.isAbsolute() //
						? EclipseFileSystem.getResource(p) //
						: project.getFile(p.toString())) //
					.map(IResource::getProjectRelativePath);
		} catch (final Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return Optional.empty();
	}

	public static boolean isFeatureModelFile(Object modelFile) {
		if (modelFile instanceof IFile) {
			final IFile file = (IFile) modelFile;
			if (file.isAccessible()) {
				return FMFormatManager.getInstance().getFormatByContent(EclipseFileSystem.getPath(file)) != null;
			}
		}
		return false;
	}

}
