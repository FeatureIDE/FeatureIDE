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
package de.ovgu.featureide.core;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.AND_COMPOSER_TO_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_OLD_NATURE_TO_;
import static de.ovgu.featureide.fm.core.localization.StringTable.COULD_NOT_SET_PERSISTANT_PROPERTY;
import static de.ovgu.featureide.fm.core.localization.StringTable.IN_PROJECT_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_COMPOSER_FOUND_IN_DESCRIPTION_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_PROJECT_DESCRIPTION_FOUND_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_RESOURCE_GIVEN_WHILE_GETTING_THE_PROJECT_DATA;
import static de.ovgu.featureide.fm.core.localization.StringTable.REMOVED;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.TimeoutException;

import javax.annotation.CheckForNull;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.ISafeRunnable;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.CompletionProposal;
import org.eclipse.jdt.core.Flags;
import org.eclipse.jdt.core.Signature;
import org.osgi.framework.BundleContext;
import org.prop4j.Node;

import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.ExtensibleFeatureProjectBuilder;
import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.internal.FeatureProject;
import de.ovgu.featureide.core.internal.ProjectChangeListener;
import de.ovgu.featureide.core.job.PrintDocumentationJob;
import de.ovgu.featureide.core.listeners.IConfigurationChangedListener;
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.core.listeners.ICurrentConfigurationListener;
import de.ovgu.featureide.core.listeners.IFeatureFolderListener;
import de.ovgu.featureide.core.listeners.IProjectListener;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.ProjectStructure;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.documentation.ContextMerger;
import de.ovgu.featureide.core.signature.documentation.FeatureModuleMerger;
import de.ovgu.featureide.core.signature.documentation.SPLMerger;
import de.ovgu.featureide.core.signature.documentation.VariantMerger;
import de.ovgu.featureide.core.signature.filter.ContextFilter;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.XMLConfFormat;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.cnf.UnkownLiteralException;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * The activator class controls the plug-in life cycle.
 *
 * @author Constanze Adler
 * @author Marcus Leich
 * @author Tom Brosch
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class CorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.core";

	private static final String COMPOSERS_ID = PLUGIN_ID + ".composers";

	private static final String BASE_FEATURE = "Base";

	private static CorePlugin plugin;

	private HashMap<IProject, IFeatureProject> featureProjectMap;

	private final LinkedList<IProjectListener> projectListeners = new LinkedList<IProjectListener>();

	private final LinkedList<ICurrentConfigurationListener> currentConfigurationListeners = new LinkedList<>();

	private final LinkedList<IConfigurationChangedListener> configurationChangedListeners = new LinkedList<>();

	private final LinkedList<IFeatureFolderListener> featureFolderListeners = new LinkedList<>();

	private final LinkedList<ICurrentBuildListener> currentBuildListeners = new LinkedList<>();

	private final ConcurrentLinkedQueue<IProject> projectsToAdd = new ConcurrentLinkedQueue<>();

	private IRunner<Void> job = null;

	/**
	 * add ResourceChangeListener to workspace to track project move/rename events at the moment project refactoring and
	 */
	private IResourceChangeListener listener;

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;

		featureProjectMap = new HashMap<>();
		for (final IProject project : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
			try {
				if (project.isOpen()) {
					// conversion for old projects
					final IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(COMPOSERS_ID);
					for (final IConfigurationElement e : config) {
						if (project.hasNature(e.getAttribute("nature"))) {
							changeOldNature(project, e.getAttribute("ID"));
						}
					}
					if (project.hasNature(FeatureProjectNature.NATURE_ID)) {
						addProject(project);
					}
				}
			} catch (final Exception e) {
				CorePlugin.getDefault().logError(e);
			}
		}
		listener = new ProjectChangeListener();
		ResourcesPlugin.getWorkspace().addResourceChangeListener(listener);

	}

	/**
	 * If the given project has the old FeatureIDE nature, it will be replaced with the actual one. Also sets the composition tool to the given ID.
	 *
	 * @param project The project
	 * @param composerID The new composer ID
	 * @throws CoreException
	 */
	private static void changeOldNature(IProject project, String composerID) throws CoreException {
		CorePlugin.getDefault()
				.logInfo(CHANGE_OLD_NATURE_TO_ + FeatureProjectNature.NATURE_ID + AND_COMPOSER_TO_ + composerID + IN_PROJECT_ + project.getName() + "'");
		final IProjectDescription description = project.getDescription();
		final String[] natures = description.getNatureIds();
		for (int i = 0; i < natures.length; i++) {
			if (natures[i].startsWith("FeatureIDE_Core.")) {
				natures[i] = FeatureProjectNature.NATURE_ID;
			}
		}
		description.setNatureIds(natures);
		project.setDescription(description, null);
		project.setPersistentProperty(IFeatureProject.composerConfigID, composerID);
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(listener);

		listener = null;
		for (final IFeatureProject data : featureProjectMap.values()) {
			data.dispose();
		}
		featureProjectMap = null;

		plugin = null;
		super.stop(context);
	}

	public void addProject(IProject project) {
		if (project == null) {
			return;
		}
		synchronized (project) {
			if (!featureProjectMap.containsKey(project) && project.isOpen()) {
				featureProjectMap.put(project, null);
				final IFeatureProject data = new FeatureProject(project);
				featureProjectMap.put(project, data);
				logInfo("Feature project " + project.getName() + " added");

				for (final IProjectListener listener : projectListeners) {
					listener.projectAdded(data);
				}

				final IStatus status = isComposable(project);

				if (status.getCode() != IStatus.OK) {
					for (final IStatus child : status.getChildren()) {
						data.createBuilderMarker(data.getProject(), child.getMessage(), -1, IMarker.SEVERITY_ERROR);
					}
					data.createBuilderMarker(data.getProject(), status.getMessage(), -1, IMarker.SEVERITY_ERROR);
				}
			}
		}
	}

	public IStatus isComposable(IProject project) {
		IProjectDescription description = null;
		try {
			description = project.getDescription();
		} catch (final CoreException e) {
			logError(e);
		}
		return isComposable(description);
	}

	public IStatus isComposable(IProjectDescription description) {
		if (description != null) {
			final String composerID = getComposerID(description);
			if (composerID != null) {
				final IComposerExtension composer = ComposerExtensionManager.getInstance().getComposerById(composerID);
				if (composer != null) {
					return composer.isComposable();
				} else {
					return new Status(IStatus.ERROR, PLUGIN_ID, "No Composer Found for ID " + composerID);
				}
			} else {
				return new Status(IStatus.ERROR, PLUGIN_ID, NO_COMPOSER_FOUND_IN_DESCRIPTION_);
			}
		} else {
			return new Status(IStatus.ERROR, PLUGIN_ID, NO_PROJECT_DESCRIPTION_FOUND_);
		}
	}

	@CheckForNull
	public String getComposerID(IProjectDescription description) {
		for (final ICommand command : description.getBuildSpec()) {
			// TODO Make Extension Point for additional Builders
			if (ExtensibleFeatureProjectBuilder.BUILDER_ID.equals(command.getBuilderName())
				|| "de.ovgu.featureide.core.mpl.MSPLBuilder".equals(command.getBuilderName())) {
				return command.getArguments().get("composer");
			}
		}
		return null;
	}

	public void removeProject(IProject project) {
		if (project == null) {
			return;
		}
		synchronized (project) {
			if (featureProjectMap.containsKey(project)) {
				final IFeatureProject featureProject = featureProjectMap.remove(project);
				// Quick fix #402
				featureProject.dispose();

				logInfo(project.getName() + REMOVED);

				for (final IProjectListener listener : projectListeners) {
					listener.projectRemoved(featureProject);
				}
			}
		}
	}

	public void addCurrentBuildListener(ICurrentBuildListener listener) {
		if (!currentBuildListeners.contains(listener)) {
			currentBuildListeners.add(listener);
		}
	}

	public void removeCurrentBuildListener(ICurrentBuildListener listener) {
		currentBuildListeners.remove(listener);
	}

	public void fireBuildUpdated(IFeatureProject featureProject) {
		for (final ICurrentBuildListener listener : currentBuildListeners) {
			listener.updateGuiAfterBuild(featureProject, featureProject.getCurrentConfiguration());
		}
	}

	public void addProjectListener(IProjectListener listener) {
		if (!projectListeners.contains(listener)) {
			projectListeners.add(listener);
		}
	}

	public void removeProjectListener(IProjectListener listener) {
		projectListeners.remove(listener);
	}

	public void addCurrentConfigurationListener(ICurrentConfigurationListener listener) {
		if (!currentConfigurationListeners.contains(listener)) {
			currentConfigurationListeners.add(listener);
		}
	}

	public void addConfigurationChangedListener(IConfigurationChangedListener listener) {
		if (!configurationChangedListeners.contains(listener)) {
			configurationChangedListeners.add(listener);
		}
	}

	public void removeCurrentConfigurationListener(ICurrentConfigurationListener listener) {
		currentConfigurationListeners.remove(listener);
	}

	public void fireCurrentConfigurationChanged(IFeatureProject featureProject) {
		for (final ICurrentConfigurationListener listener : currentConfigurationListeners) {
			listener.currentConfigurationChanged(featureProject);
		}
	}

	public void fireConfigurationChanged(IFeatureProject featureProject) {
		for (final IConfigurationChangedListener listener : configurationChangedListeners) {
			listener.configurationChanged(featureProject);
		}
	}

	public void addFeatureFolderListener(IFeatureFolderListener listener) {
		if (!featureFolderListeners.contains(listener)) {
			featureFolderListeners.add(listener);
		}
	}

	public void removeFeatureFolderListener(IFeatureFolderListener listener) {
		featureFolderListeners.remove(listener);
	}

	public void fireFeatureFolderChanged(IFolder folder) {
		for (final IFeatureFolderListener listener : featureFolderListeners) {
			listener.featureFolderChanged(folder);
		}
	}

	/**
	 * Setups the projects structure.<br> Starts composer specific changes of the project structure, after adding the FeatureIDE nature to a project.
	 */
	public static void setupProject(final IProject project, String compositionToolID, final String sourcePath, final String configPath, final String buildPath,
			boolean shouldCreateSourceFolder, boolean shouldCreateBuildFolder) {
		final IComposerExtensionClass composer = getComposer(compositionToolID);
		setupFeatureProject(project, compositionToolID, sourcePath, configPath, buildPath, false, false, shouldCreateSourceFolder, shouldCreateBuildFolder);

		if (composer != null) {
			final ISafeRunnable runnable = new ISafeRunnable() {

				@Override
				public void handleException(Throwable e) {
					getDefault().logError(e);
				}

				@Override
				public void run() throws Exception {
					runProjectConversion(project, sourcePath, configPath, buildPath, composer);
					addFeatureNatureToProject(project);
				}
			};
			SafeRunner.run(runnable);
		}
		setProjectProperties(project, compositionToolID, sourcePath, configPath, buildPath, false);
	}

	/**
	 * Composer specific changes of the project structure, after adding the FeatureIDE nature to a project.<br> Moves the files of the source folder to the
	 * features folder(composer specific)<br> Creates a configuration file, where the base feature is selected, to automatically build the project.
	 */
	protected static void runProjectConversion(IProject project, String sourcePath, String configPath, String buildPath, IComposerExtensionClass composer)
			throws IOException {
		try {
			if (composer.hasSourceFolder() || composer.hasFeatureFolder()) {
				project.getFolder(buildPath).deleteMarkers(null, true, IResource.DEPTH_INFINITE);

				final IFolder source = project.getFolder(buildPath);
				IFolder destination = !"".equals(sourcePath) ? project.getFolder(sourcePath).getFolder(BASE_FEATURE) : null;
				if (!composer.postAddNature(source, destination) && !"".equals(sourcePath)) {
					if (!composer.hasFeatureFolder()) {
						/** if project does not use feature folder, use the source path directly **/
						destination = project.getFolder(sourcePath);
					}
					if (!destination.exists()) {
						destination.create(false, true, null);
					}
					/** moves all files of the old source folder to the destination **/
					for (final IResource res : source.members()) {
						res.move(destination.getFile(res.getName()).getFullPath(), true, null);
					}
				}
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Setups the project.<br> Creates folders<br> Adds the compiler(if necessary)<br> Adds the FeatureIDE nature<br> Creates the feature model
	 *
	 * @param addCompiler <code>false</code> if the project already has a compiler
	 */
	public static void setupFeatureProject(final IProject project, String compositionToolID, final String sourcePath, final String configPath,
			final String buildPath, boolean addCompiler, boolean addNature, boolean shouldCreateSourceFolder, boolean shouldCreateBuildFolder) {
		final IComposerExtensionClass composer = getComposer(compositionToolID);
		createProjectStructure(project, sourcePath, configPath, buildPath, composer, shouldCreateSourceFolder, shouldCreateBuildFolder);

		final IFeatureModel featureModel = createFeatureModelFile(project);
		createConfigFile(project, configPath, featureModel, "default.");

		if ((composer != null) && addCompiler) {
			final ISafeRunnable runnable = new ISafeRunnable() {

				@Override
				public void handleException(Throwable e) {
					getDefault().logError(e);
				}

				@Override
				public void run() throws Exception {
					composer.addCompiler(project, sourcePath, configPath, buildPath);
				}
			};
			SafeRunner.run(runnable);
		}
		setProjectProperties(project, compositionToolID, sourcePath, configPath, buildPath, addNature);
	}

	private static void setProjectProperties(final IProject project, String compositionToolID, final String sourcePath, final String configPath,
			final String buildPath, boolean addNature) {
		try {
			project.setPersistentProperty(IFeatureProject.composerConfigID, compositionToolID);
			project.setPersistentProperty(IFeatureProject.buildFolderConfigID, buildPath);
			project.setPersistentProperty(IFeatureProject.configFolderConfigID, configPath);
			project.setPersistentProperty(IFeatureProject.sourceFolderConfigID, sourcePath);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(COULD_NOT_SET_PERSISTANT_PROPERTY, e);
		}
		if (addNature) {
			addFeatureNatureToProject(project);
		}
	}

	private static IComposerExtensionClass getComposer(String compositionToolID) {
		IComposerExtensionClass composer = null;
		for (final IConfigurationElement element : Platform.getExtensionRegistry().getConfigurationElementsFor(COMPOSERS_ID)) {
			if (element.getAttribute("id").equals(compositionToolID)) {
				try {
					final Object o = element.createExecutableExtension("class");
					if (o instanceof IComposerExtensionClass) {
						composer = (IComposerExtensionClass) o;
					}
				} catch (final CoreException e) {
					getDefault().logError(e);
				}
				break;
			}
		}
		return composer;
	}

	private static void addFeatureNatureToProject(IProject project) {
		try {
			// check if the nature was already added
			if (!project.isAccessible() || project.hasNature(FeatureProjectNature.NATURE_ID)) {
				return;
			}

			// add the FeatureIDE nature
			CorePlugin.getDefault().logInfo("Add Nature (" + FeatureProjectNature.NATURE_ID + ") to " + project.getName());
			final IProjectDescription description = project.getDescription();
			final String[] natures = description.getNatureIds();
			final String[] newNatures = new String[natures.length + 1];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			newNatures[natures.length] = FeatureProjectNature.NATURE_ID;
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	public static IFolder createFolder(IProject project, String name) {
		if ("".equals(name)) {
			return null;
		}
		final String[] names = name.split("[/]");
		IFolder folder = null;
		for (final String folderName : names) {
			if (folder == null) {
				folder = project.getFolder(folderName);
			} else {
				folder = folder.getFolder(folderName);
			}
			try {
				if (!folder.exists()) {
					folder.create(false, true, null);
				}
			} catch (final CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
		return folder;
	}

	public static IFolder getFolder(IProject project, String name) {
		if ("".equals(name)) {
			return null;
		}
		final String[] names = name.split("[/]");
		IFolder folder = null;
		for (final String folderName : names) {
			if (folder == null) {
				folder = project.getFolder(folderName);
			} else {
				folder = folder.getFolder(folderName);
			}
		}
		return folder;
	}

	/**
	 * Creates the source-, features- and build-folder at the given paths.<br> Also creates the bin folder if necessary.<br> Creates the default feature model.
	 */
	private static void createProjectStructure(IProject project, String sourcePath, String configPath, String buildPath, IComposerExtensionClass composer,
			boolean shouldCreateSourceFolder, boolean shouldCreateBuildFolder) {
		try {
			/** just create the bin folder if project has only the FeatureIDE Nature **/
			if ((project.getDescription().getNatureIds().length == 1) && project.hasNature(FeatureProjectNature.NATURE_ID)) {
				if (!("".equals(buildPath) && "".equals(sourcePath)) && shouldCreateBuildFolder && composer.hasSource()) {
					createFolder(project, "bin");
				}
			}
		} catch (final CoreException e) {
			getDefault().logError(e);
		}
		if (composer.hasSource()) {
			if (shouldCreateSourceFolder) {
				createFolder(project, sourcePath);
			}
			if (shouldCreateBuildFolder) {
				createFolder(project, buildPath);
			}
		}
		createFolder(project, configPath);
	}

	private static IFeatureModel createFeatureModelFile(IProject project) {
		final Path modelPath = Paths.get(project.getFile("model.xml").getLocationURI());

		if (!modelPath.toFile().exists()) {
			final XmlFeatureModelFormat format = new XmlFeatureModelFormat();
			IFeatureModelFactory factory;
			try {
				factory = FMFactoryManager.getFactory(modelPath.toString(), format);
			} catch (final NoSuchExtensionException e) {
				Logger.logError(e);
				factory = FMFactoryManager.getDefaultFactory();
			}
			final IFeatureModel featureModel = factory.createFeatureModel();
			FMComposerManager.getFMComposerExtension(project);
			featureModel.createDefaultValues(project.getName());

			SimpleFileHandler.save(modelPath, featureModel, format);
			return featureModel;
		}
		return null;
	}

	private static Configuration createConfigFile(IProject project, String configPath, IFeatureModel featureModel, final String configName) {
		final XMLConfFormat configFormat = new XMLConfFormat();
		final IFile file = project.getFolder(configPath).getFile(configName + configFormat.getSuffix());
		final Configuration config = new Configuration(featureModel);
		SimpleFileHandler.save(Paths.get(file.getLocationURI()), config, configFormat);
		return config;
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static CorePlugin getDefault() {
		return plugin;
	}

	/**
	 * returns an unmodifiable Collection of all ProjectData items, or <code>null</code> if plugin is not loaded
	 *
	 * @return
	 */
	public static Collection<IFeatureProject> getFeatureProjects() {
		if (getDefault() == null) {
			return null;
		}
		return Collections.unmodifiableCollection(getDefault().featureProjectMap.values());
	}

	/**
	 * returns the ProjectData object associated with the given resource
	 *
	 * @param res
	 * @return <code>null</code> if there is no associated project, no active instance of this plug-in or resource is the workspace root
	 */
	@CheckForNull
	public static IFeatureProject getFeatureProject(IResource res) {
		if (res == null) {
			getDefault().logWarning(NO_RESOURCE_GIVEN_WHILE_GETTING_THE_PROJECT_DATA);
			return null;
		}
		final IProject prj = res.getProject();
		if (prj == null) {
			return null;
		}
		return getDefault().featureProjectMap.get(prj);
	}

	public static boolean hasProjectData(IResource res) {
		return getFeatureProject(res) != null;
	}

	/**
	 * A linear job to add a project. This is necessary if many projects will be add at the same time.
	 *
	 * @param project
	 */
	public void addProjectToList(IProject project) {
		if (!featureProjectMap.containsKey(project) && project.isOpen() && !projectsToAdd.contains(project)) {
			projectsToAdd.offer(project);
			scheduleAddJob();
		}
	}

	private void scheduleAddJob() {
		synchronized (this) {
			if (job == null) {
				job = LongRunningWrapper.getRunner(new AddingProjectsMethod(), ADD_PROJECT);
				job.addJobFinishedListener(new JobFinishListener<Void>() {

					@Override
					public void jobFinished(IJob<Void> finishedJob) {
						synchronized (CorePlugin.this) {
							job = null;
						}
						if (!projectsToAdd.isEmpty()) {
							scheduleAddJob();
						}
					}
				});
				job.schedule();
			}
		}
	}

	private class AddingProjectsMethod implements LongRunningMethod<Void> {

		@Override
		public Void execute(IMonitor monitor) throws Exception {
			monitor.setRemainingWork(projectsToAdd.size());
			while (!projectsToAdd.isEmpty()) {
				final IProject project = projectsToAdd.poll();
				final IMonitor subTask = monitor.subTask(1);
				subTask.setTaskName(project.getName());
				addProject(project);
				subTask.step();
			}
			return null;
		}
	}

	public List<CompletionProposal> extendedModules_getCompl(IFeatureProject featureProject, String featureName) {
		final LinkedList<CompletionProposal> ret_List = new LinkedList<CompletionProposal>();
		final ProjectSignatures signatures = featureProject.getProjectSignatures();

		if (signatures != null) {
			final SignatureIterator it = signatures.iterator();
			final int featureID = signatures.getFeatureID(featureName);
			if (featureID == -1) {
				return Collections.emptyList();
			}
			it.addFilter(new ContextFilter(featureName, signatures));

			while (it.hasNext()) {
				final AbstractSignature curMember = it.next();
				CompletionProposal pr = null;

				if (curMember instanceof AbstractMethodSignature) {
					pr = CompletionProposal.create(CompletionProposal.METHOD_REF, 0);
					final AbstractMethodSignature methSig = (AbstractMethodSignature) curMember;
					final List<String> sig = methSig.getParameterTypes();

					// TODO differentiate between possible types
					char[][] c = new char[][] { {} };
					if (sig.size() > 0) {
						c = new char[sig.size()][];
						int i = 0;
						for (final String parameterType : sig) {
							final String parameterTypeToChar = "L" + parameterType + ";";
							c[i++] = parameterTypeToChar.toCharArray();
						}
					}

					final String returnType = "L" + methSig.getReturnType() + ";";
					pr.setSignature(Signature.createMethodSignature(c, returnType.toCharArray()));
					final String declType = "L" + methSig.getFullName().replaceAll("." + methSig.getName(), "") + ";";
					pr.setDeclarationSignature(declType.toCharArray());
				} else if (curMember instanceof AbstractFieldSignature) {
					pr = CompletionProposal.create(CompletionProposal.FIELD_REF, 0);
				} else if (curMember instanceof AbstractClassSignature) {
					pr = CompletionProposal.create(CompletionProposal.TYPE_REF, 0);
					pr.setSignature(Signature.createTypeSignature(curMember.getFullName(), true).toCharArray());
				}

				if (pr != null) {
					pr.setFlags(getFlagOfSignature(curMember));
					pr.setName(curMember.getName().toCharArray());
					pr.setCompletion(curMember.getName().toCharArray());

					ret_List.add(pr);
				}
			}
		}
		return ret_List;
	}

	private int getFlagOfSignature(AbstractSignature element) {
		if (element instanceof AbstractMethodSignature) {
			// TODO add constructor icon
			switch (((AbstractMethodSignature) element).getVisibilty()) {
			case AbstractSignature.VISIBILITY_DEFAULT:
				return Flags.AccDefault;
			case AbstractSignature.VISIBILITY_PRIVATE:
				return Flags.AccPrivate;
			case AbstractSignature.VISIBILITY_PROTECTED:
				return Flags.AccProtected;
			case AbstractSignature.VISIBILITY_PUBLIC:
				return Flags.AccPublic;
			}
		} else if (element instanceof AbstractFieldSignature) {
			switch (((AbstractFieldSignature) element).getVisibilty()) {
			case AbstractSignature.VISIBILITY_DEFAULT:
				return Flags.AccDefault;
			case AbstractSignature.VISIBILITY_PRIVATE:
				return Flags.AccPrivate;
			case AbstractSignature.VISIBILITY_PROTECTED:
				return Flags.AccProtected;
			case AbstractSignature.VISIBILITY_PUBLIC:
				return Flags.AccPublic;
			}
		}
		return 0;
	}

	public ProjectStructure extendedModules_getStruct(final IFeatureProject project, final String featureName) {
		final ProjectSignatures signatures = project.getProjectSignatures();
		if ((signatures != null) && (signatures.getFeatureID(featureName) != -1)) {
			final SignatureIterator it = signatures.iterator();
			// TODO check
			if (featureName != null) {
				it.addFilter(new ContextFilter(featureName, signatures));
			}
			return new ProjectStructure(it);
		}
		return null;
	}

	public void buildContextDocumentation(List<IProject> pl, String options, String featureName) {
		final ArrayList<JobArguments> arguments = new ArrayList<>(pl.size());
		for (final IProject iProject : pl) {
			arguments
					.add(new PrintDocumentationJob.Arguments("Docu_Context_" + featureName, options.split("\\s+"), new ContextMerger(), featureName, iProject));
		}
		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

	public void buildVariantDocumentation(List<IProject> pl, String options) {
		final ArrayList<JobArguments> arguments = new ArrayList<>(pl.size());
		for (final IProject iProject : pl) {
			arguments.add(new PrintDocumentationJob.Arguments("Docu_Variant", options.split("\\s+"), new VariantMerger(), null, iProject));
		}
		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

	public void buildFeatureDocumentation(List<IProject> pl, String options, String featureName) {
		final ArrayList<JobArguments> arguments = new ArrayList<>(pl.size());
		for (final IProject iProject : pl) {
			arguments.add(new PrintDocumentationJob.Arguments("Docu_Feature_" + featureName, options.split("\\s+"), new FeatureModuleMerger(), featureName,
					iProject));
		}
		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

	public void buildSPLDocumentation(List<IProject> pl, String options) {
		final ArrayList<JobArguments> arguments = new ArrayList<>(pl.size());
		for (final IProject iProject : pl) {
			arguments.add(new PrintDocumentationJob.Arguments("Docu_SPL", options.split("\\s+"), new SPLMerger(), null, iProject));
		}
		FMCorePlugin.getDefault().startJobs(arguments, true);
	}

	public static Node removeFeatures(IFeatureModel featureModel, Collection<String> removeFeatures) throws TimeoutException, UnkownLiteralException {
		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel, removeFeatures);
		nodeCreator.setCnfType(AdvancedNodeCreator.CNFType.Regular);
		return nodeCreator.createNodes();
	}

}
