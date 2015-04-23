/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

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
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.ISafeRunnable;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.CompletionProposal;
import org.eclipse.jdt.core.Flags;
import org.eclipse.jdt.core.Signature;
import org.osgi.framework.BundleContext;

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
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author Constanze Adler
 * @author Marcus Leich
 * @author Tom Brosch
 * @author Thomas Thuem
 */
public class CorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.core";

	private static final String COMPOSERS_ID = PLUGIN_ID + ".composers";

	private static final String BASE_FEATURE = "Base";

	private static CorePlugin plugin;

	private HashMap<IProject, IFeatureProject> featureProjectMap;

	private LinkedList<IProjectListener> projectListeners = new LinkedList<IProjectListener>();

	private LinkedList<ICurrentConfigurationListener> currentConfigurationListeners = new LinkedList<ICurrentConfigurationListener>();

	private LinkedList<IConfigurationChangedListener> configurationChangedListeners = new LinkedList<IConfigurationChangedListener>();

	private LinkedList<IFeatureFolderListener> featureFolderListeners = new LinkedList<IFeatureFolderListener>();

	private LinkedList<ICurrentBuildListener> currentBuildListeners = new LinkedList<ICurrentBuildListener>();

	private LinkedList<IProject> projectsToAdd = new LinkedList<IProject>();

	private Job job = null;

	private int couterAddProjects = 0;

	/**
	 * add ResourceChangeListener to workspace to track project move/rename
	 * events at the moment project refactoring and
	 */
	private IResourceChangeListener listener;

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;

		featureProjectMap = new HashMap<IProject, IFeatureProject>();
		listener = new ProjectChangeListener();
		ResourcesPlugin.getWorkspace().addResourceChangeListener(listener);
		for (final IProject project : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
			try {
				if (project.isOpen()) {
					// conversion for old projects
					IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(COMPOSERS_ID);
					for (IConfigurationElement e : config) {
						if (project.hasNature(e.getAttribute("nature"))) {
							changeOldNature(project, e.getAttribute("ID"));
						}
					}
					if (project.hasNature(FeatureProjectNature.NATURE_ID))
						addProject(project);
				}
			} catch (Exception e) {
				CorePlugin.getDefault().logError(e);
			}
		}

	}

	/**
	 * If the given project has the old FeatureIDE nature, it will be replaced with the actual one.
	 * Also sets the composition tool to the given ID.
	 * 
	 * @param project The project
	 * @param composerID The new composer ID
	 * @throws CoreException
	 */
	private static void changeOldNature(IProject project, String composerID) throws CoreException {
		CorePlugin.getDefault().logInfo(
				"Change old nature to '" + FeatureProjectNature.NATURE_ID + "' and composer to '" + composerID + "' in project '" + project.getName() + "'");
		IProjectDescription description = project.getDescription();
		String[] natures = description.getNatureIds();
		for (int i = 0; i < natures.length; i++)
			if (natures[i].startsWith("FeatureIDE_Core."))
				natures[i] = FeatureProjectNature.NATURE_ID;
		description.setNatureIds(natures);
		project.setDescription(description, null);
		project.setPersistentProperty(IFeatureProject.composerConfigID, composerID);
	}

	public void stop(BundleContext context) throws Exception {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(listener);

		listener = null;
		for (IFeatureProject data : featureProjectMap.values())
			data.dispose();
		featureProjectMap = null;

		plugin = null;
		super.stop(context);
	}

	public void addProject(IProject project) {
		if (featureProjectMap.containsKey(project) || !project.isOpen())
			return;

		IFeatureProject data = new FeatureProject(project);
		featureProjectMap.put(project, data);
		logInfo("Feature project " + project.getName() + " added");

		for (IProjectListener listener : projectListeners)
			listener.projectAdded(data);

		final IStatus status = isComposable(project);

		if (status.getCode() != Status.OK) {
			for (IStatus child : status.getChildren()) {
				data.createBuilderMarker(data.getProject(), child.getMessage(), -1, IMarker.SEVERITY_ERROR);
			}
			data.createBuilderMarker(data.getProject(), status.getMessage(), -1, IMarker.SEVERITY_ERROR);
		}
	}

	public IStatus isComposable(IProject project) {
		IProjectDescription description = null;
		try {
			description = project.getDescription();
		} catch (CoreException e) {
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
					return new Status(Status.ERROR, PLUGIN_ID, "No Composer Found for ID " + composerID);
				}
			} else {
				return new Status(Status.ERROR, PLUGIN_ID, "No Composer Found in Description.");
			}
		} else {
			return new Status(Status.ERROR, PLUGIN_ID, "No Project Description Found.");
		}
	}

	@CheckForNull
	public String getComposerID(IProjectDescription description) {
		for (ICommand command : description.getBuildSpec()) {
			//TODO Make Extension Point for additional Builders
			if (ExtensibleFeatureProjectBuilder.BUILDER_ID.equals(command.getBuilderName())
					|| "de.ovgu.featureide.core.mpl.MSPLBuilder".equals(command.getBuilderName())) {
				return command.getArguments().get("composer");
			}
		}
		return null;
	}

	public void removeProject(IProject project) {
		if (!featureProjectMap.containsKey(project))
			return;

		IFeatureProject featureProject = featureProjectMap.remove(project);
		logInfo(project.getName() + " removed");

		for (IProjectListener listener : projectListeners)
			listener.projectRemoved(featureProject);
	}

	public void addCurrentBuildListener(ICurrentBuildListener listener) {
		if (!currentBuildListeners.contains(listener))
			currentBuildListeners.add(listener);
	}

	public void removeCurrentBuildListener(ICurrentBuildListener listener) {
		currentBuildListeners.remove(listener);
	}

	public void fireBuildUpdated(IFeatureProject featureProject) {
		for (ICurrentBuildListener listener : currentBuildListeners)
			listener.updateGuiAfterBuild(featureProject, featureProject.getCurrentConfiguration());
	}

	public void addProjectListener(IProjectListener listener) {
		if (!projectListeners.contains(listener))
			projectListeners.add(listener);
	}

	public void removeProjectListener(IProjectListener listener) {
		projectListeners.remove(listener);
	}

	public void addCurrentConfigurationListener(ICurrentConfigurationListener listener) {
		if (!currentConfigurationListeners.contains(listener))
			currentConfigurationListeners.add(listener);
	}

	public void addConfigurationChangedListener(IConfigurationChangedListener listener) {
		if (!configurationChangedListeners.contains(listener))
			configurationChangedListeners.add(listener);
	}

	public void removeCurrentConfigurationListener(ICurrentConfigurationListener listener) {
		currentConfigurationListeners.remove(listener);
	}

	public void fireCurrentConfigurationChanged(IFeatureProject featureProject) {
		for (ICurrentConfigurationListener listener : currentConfigurationListeners)
			listener.currentConfigurationChanged(featureProject);
	}

	public void fireConfigurationChanged(IFeatureProject featureProject) {
		for (IConfigurationChangedListener listener : configurationChangedListeners)
			listener.configurationChanged(featureProject);
	}

	public void addFeatureFolderListener(IFeatureFolderListener listener) {
		if (!featureFolderListeners.contains(listener))
			featureFolderListeners.add(listener);
	}

	public void removeFeatureFolderListener(IFeatureFolderListener listener) {
		featureFolderListeners.remove(listener);
	}

	public void fireFeatureFolderChanged(IFolder folder) {
		for (IFeatureFolderListener listener : featureFolderListeners)
			listener.featureFolderChanged(folder);
	}

	/**
	 * Setups the projects structure.<br>
	 * Starts composer specific changes of the project structure,
	 * after adding the FeatureIDE nature to a project.
	 */
	public static void setupProject(final IProject project, String compositionToolID, final String sourcePath, final String configPath, final String buildPath) {
		setupFeatureProject(project, compositionToolID, sourcePath, configPath, buildPath, false);

		IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(COMPOSERS_ID);
		try {
			for (IConfigurationElement e : config) {
				if (e.getAttribute("id").equals(compositionToolID)) {
					final Object o = e.createExecutableExtension("class");
					if (o instanceof IComposerExtensionClass) {

						ISafeRunnable runnable = new ISafeRunnable() {
							public void handleException(Throwable e) {
								getDefault().logError(e);
							}

							public void run() throws Exception {
								runProjectConversion(project, sourcePath, configPath, buildPath, (IComposerExtensionClass) o);
							}
						};
						SafeRunner.run(runnable);
					}
					break;
				}
			}
		} catch (CoreException e) {
			getDefault().logError(e);
		}

	}

	/**
	 * Composer specific changes of the project structure,
	 * after adding the FeatureIDE nature to a project.<br>
	 * Moves the files of the source folder to the features folder(composer specific)<br>
	 * Creates a configuration file, where the base feature is selected, to automatically build the project.
	 */
	protected static void runProjectConversion(IProject project, String sourcePath, String configPath, String buildPath, IComposerExtensionClass composer)
			throws IOException {
		try {
			if (composer.hasSourceFolder() || composer.hasFeatureFolder()) {
				project.getFolder(buildPath).deleteMarkers(null, true, IResource.DEPTH_INFINITE);

				IFolder source = project.getFolder(buildPath);
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
					for (IResource res : source.members()) {
						res.move(destination.getFile(res.getName()).getFullPath(), true, null);
					}
				}
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		/**
		 * create a configuration to automatically build
		 * the project after adding the FeatureIDE nature
		 **/
		IFile configFile = project.getFolder(configPath).getFile(project.getName().split("[-]")[0] + "." + composer.getConfigurationExtension());
		FileWriter fw = null;
		try {
			fw = new FileWriter(configFile.getRawLocation().toFile());
			fw.write(BASE_FEATURE);

			configFile.create(null, true, null);
			configFile.refreshLocal(IResource.DEPTH_ZERO, null);
		} catch (CoreException e) {
			// Avoid file exist error
			// Has no negative effect
		} finally {
			if (fw != null) {
				fw.close();
			}
		}
	}

	/**
	 * Setups the project.<br>
	 * Creates folders<br>
	 * Adds the compiler(if necessary)<br>
	 * Adds the FeatureIDE nature<br>
	 * Creates the feature model
	 * 
	 * @param addCompiler <code>false</code> if the project already has a compiler
	 */
	public static void setupFeatureProject(final IProject project, String compositionToolID, final String sourcePath, final String configPath,
			final String buildPath, boolean addCompiler) {
		createProjectStructure(project, sourcePath, configPath, buildPath);

		if (addCompiler) {
			try {
				IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(COMPOSERS_ID);
				for (IConfigurationElement e : config) {
					if (e.getAttribute("id").equals(compositionToolID)) {
						final Object o = e.createExecutableExtension("class");
						if (o instanceof IComposerExtensionClass) {

							ISafeRunnable runnable = new ISafeRunnable() {
								public void handleException(Throwable e) {
									getDefault().logError(e);
								}

								public void run() throws Exception {
									((IComposerExtensionClass) o).addCompiler(project, sourcePath, configPath, buildPath);

									final String path = project.getFolder(configPath).getRawLocation() + "/default."
											+ ((IComposerExtensionClass) o).getConfigurationExtension();
									new File(path).createNewFile();
									project.getFolder(configPath).refreshLocal(IResource.DEPTH_INFINITE, null);
								}
							};
							SafeRunner.run(runnable);
						}
						break;
					}
				}
			} catch (CoreException e) {
				getDefault().logError(e);
			}
		}
		try {
			project.setPersistentProperty(IFeatureProject.composerConfigID, compositionToolID);
			project.setPersistentProperty(IFeatureProject.buildFolderConfigID, buildPath);
			project.setPersistentProperty(IFeatureProject.configFolderConfigID, configPath);
			project.setPersistentProperty(IFeatureProject.sourceFolderConfigID, sourcePath);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError("Could not set persistant property", e);
		}
		addFeatureNatureToProject(project);
	}

	private static void addFeatureNatureToProject(IProject project) {
		try {
			// check if the nature was already added
			if (!project.isAccessible() || project.hasNature(FeatureProjectNature.NATURE_ID)) {
				return;
			}

			// add the FeatureIDE nature
			CorePlugin.getDefault().logInfo("Add Nature (" + FeatureProjectNature.NATURE_ID + ") to " + project.getName());
			IProjectDescription description = project.getDescription();
			String[] natures = description.getNatureIds();
			String[] newNatures = new String[natures.length + 1];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			newNatures[natures.length] = FeatureProjectNature.NATURE_ID;
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	public static IFolder createFolder(IProject project, String name) {
		if ("".equals(name)) {
			return null;
		}
		String[] names = name.split("[/]");
		IFolder folder = null;
		for (String folderName : names) {
			if (folder == null) {
				folder = project.getFolder(folderName);
			} else {
				folder = folder.getFolder(folderName);
			}
			try {
				if (!folder.exists()) {
					folder.create(false, true, null);
				}
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
		return folder;
	}

	/**
	 * Creates the source-, features- and build-folder at the given paths.<br>
	 * Also creates the bin folder if necessary.<br>
	 * Creates the default feature model.
	 * 
	 * @param project
	 * @param sourcePath
	 * @param configPath
	 * @param buildPath
	 */
	private static void createProjectStructure(IProject project, String sourcePath, String configPath, String buildPath) {
		try {
			/** just create the bin folder if project has only the FeatureIDE Nature **/
			if (project.getDescription().getNatureIds().length == 1 && project.hasNature(FeatureProjectNature.NATURE_ID)) {
				if ("".equals(buildPath) && "".equals(sourcePath)) {
					createFolder(project, "bin");
				}
			}
		} catch (CoreException e) {
			getDefault().logError(e);
		}
		createFolder(project, sourcePath);
		createFolder(project, configPath);
		createFolder(project, buildPath);
		FeatureModel featureModel = new FeatureModel();
		featureModel.initFMComposerExtension(project);
		featureModel.createDefaultValues(project.getName());
		try {
			new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(featureModel)).writeToFile(project.getFile("model.xml"));
		} catch (CoreException e) {
			CorePlugin.getDefault().logError("Error while creating feature model", e);
		}

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
		if (getDefault() == null)
			return null;
		return Collections.unmodifiableCollection(getDefault().featureProjectMap.values());
	}

	/**
	 * returns the ProjectData object associated with the given resource
	 * 
	 * @param res
	 * @return <code>null</code> if there is no associated project, no active
	 *         instance of this plug-in or resource is the workspace root
	 */
	@CheckForNull
	public static IFeatureProject getFeatureProject(IResource res) {
		if (res == null) {
			getDefault().logWarning("No resource given while getting the project data");
			return null;
		}
		IProject prj = res.getProject();
		if (prj == null) {
			return null;
		}
		return getDefault().featureProjectMap.get(prj);
	}

	public static boolean hasProjectData(IResource res) {
		return getFeatureProject(res) != null;
	}

	/**
	 * @return A list of all valid configuration extensions
	 */
	public LinkedList<String> getConfigurationExtensions() {
		LinkedList<String> extensions = new LinkedList<String>();
		extensions.add("config");
		extensions.add("equation");
		extensions.add("expression");
		return extensions;
	}

	/**
	 * A linear job to add a project. This is necessary if many projects will be add at the same time.
	 * 
	 * @param project
	 */
	public void addProjectToList(IProject project) {
		if (projectsToAdd.contains(project)) {
			return;
		}
		if (featureProjectMap.containsKey(project) || !project.isOpen()) {
			return;
		}

		projectsToAdd.add(project);
		if (job == null) {
			job = new Job("Add Project") {
				@Override
				public IStatus run(IProgressMonitor monitor) {
					addProjects(monitor);
					monitor.beginTask("", 1);
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.SHORT);
			job.schedule();
		}

		if (job.getState() == Job.NONE) {
			couterAddProjects = 0;
			job.schedule();
		}
	}

	protected void addProjects(IProgressMonitor monitor) {
		if (projectsToAdd.isEmpty()) {
			monitor.done();
			return;
		}

		while (!projectsToAdd.isEmpty()) {
			IProject project = projectsToAdd.getFirst();
			projectsToAdd.remove(project);

			monitor.beginTask("", projectsToAdd.size() + couterAddProjects);
			monitor.worked(++couterAddProjects);
			monitor.subTask("Add project " + project.getName());

			addProject(project);

		}
		addProjects(monitor);
	}

	public List<CompletionProposal> extendedModules_getCompl(IFeatureProject featureProject, String featureName) {
		final LinkedList<CompletionProposal> ret_List = new LinkedList<CompletionProposal>();
		final ProjectSignatures signatures = featureProject.getProjectSignatures();

		if (signatures != null) {
			SignatureIterator it = signatures.iterator();
			it.addFilter(new ContextFilter(featureName, signatures));

			while (it.hasNext()) {
				AbstractSignature curMember = it.next();
				CompletionProposal pr = null;

				if (curMember instanceof AbstractMethodSignature) {
					pr = CompletionProposal.create(CompletionProposal.METHOD_REF, 0);
					final AbstractMethodSignature methSig = (AbstractMethodSignature) curMember;
					final List<String> sig = methSig.getParameterTypes();

					//TODO differentiate between possible types
					char[][] c = new char[][] { {} };
					if (sig.size() > 0) {
						c = new char[sig.size()][];
						int i = 0;
						for (String parameterType : sig) {
							String parameterTypeToChar = "L" + parameterType + ";";
							c[i++] = parameterTypeToChar.toCharArray();
						}
					}

					String returnType = "L" + methSig.getReturnType() + ";";
					pr.setSignature(Signature.createMethodSignature(c, returnType.toCharArray()));
					String declType = "L" + methSig.getFullName().replaceAll("." + methSig.getName(), "") + ";";
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
			//TODO add constructor icon
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
		if (signatures != null) {
			SignatureIterator it = signatures.iterator();
			//TODO check
			if (featureName != null) {
				it.addFilter(new ContextFilter(featureName, signatures));
			}
			return new ProjectStructure(it);
		}
		return null;
	}

	public void buildContextDocumentation(List<IProject> pl, String options, String featureName) {
		final PrintDocumentationJob.Arguments args = new PrintDocumentationJob.Arguments(
				"Docu_Context_" + featureName, options.split("\\s+"), new ContextMerger(), featureName);

		FMCorePlugin.getDefault().startJobs(pl, args, true);
	}

	public void buildVariantDocumentation(List<IProject> pl, String options) {
		final PrintDocumentationJob.Arguments args = new PrintDocumentationJob.Arguments(
				"Docu_Variant", options.split("\\s+"), new VariantMerger(), null);

		FMCorePlugin.getDefault().startJobs(pl, args, true);
	}

	public void buildFeatureDocumentation(List<IProject> pl, String options, String featureName) {
		final PrintDocumentationJob.Arguments args = new PrintDocumentationJob.Arguments(
				"Docu_Feature_" + featureName, options.split("\\s+"), new FeatureModuleMerger(), featureName);

		FMCorePlugin.getDefault().startJobs(pl, args, true);
	}

	public void buildSPLDocumentation(List<IProject> pl, String options) {
		final PrintDocumentationJob.Arguments args = new PrintDocumentationJob.Arguments(
				"Docu_SPL", options.split("\\s+"), new SPLMerger(), null);

		FMCorePlugin.getDefault().startJobs(pl, args, true);
	}

}
