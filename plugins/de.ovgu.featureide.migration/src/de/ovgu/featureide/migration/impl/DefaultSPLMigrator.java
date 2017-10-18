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
package de.ovgu.featureide.migration.impl;

import static de.ovgu.featureide.fm.core.localization.StringTable.CLASSPATH_OF_PROJECT_TO_MIGRATE_IS_NULL;
import static de.ovgu.featureide.fm.core.localization.StringTable.DESTINATIONFOLDER_NOT_ACCESSIBLE_OR_WRONG_PATH;
import static de.ovgu.featureide.fm.core.localization.StringTable.INTERNAL_ASSERT_MESSAGE_PROJECT_IS_NULL;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_OPEN_;
import static de.ovgu.featureide.fm.core.localization.StringTable.JAVA_PROJECTS_COULD_NOT_BE_CREATED;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_PROJECTS_WERE_SELECTED_FOR_MIGRATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROJECT_PROPERTIES_COULD_NOT_BE_COPIED_COMMA__BECAUSE_IT_DOES_NOT_EXIST_;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;
import de.ovgu.featureide.ui.migration.wizard.SPLMigrationDialogSettingsPage;

/**
 * @author Marcus Pinnecke (Feature interface)
 */
@SuppressWarnings(RESTRICTION)
public abstract class DefaultSPLMigrator implements ISPLMigrator {

	public static final String PROJECT_PROPERTIES_FILE_NAME = "project.properties";
	public static final String DEFAULT_PROJECT_NAME = "migratedSPL";
	public static final String ANDROID_NATURE = "com.android.ide.eclipse.adt.AndroidNature";

	/**
	 * The new project which contains the software product line, when the migration is done.
	 */
	protected IProject newProject;

	/**
	 * The (Java) projects which are going to be migrated into a SPL.
	 */
	protected Set<IProject> projects;

	protected MigrationConfigurationData configurationData;

	public DefaultSPLMigrator() {
		super();
	}

	@Override
	public void registerProjectsForMigration(Set<IProject> projects) {
		if ((projects == null) || projects.isEmpty()) {
			throw new IllegalArgumentException(NO_PROJECTS_WERE_SELECTED_FOR_MIGRATION);
		}

		this.projects = projects;
	}

	@Override
	public void migrate(MigrationConfigurationData configurationData) {
		this.configurationData = configurationData;

		createProject();

		migrateProjects();

		final IFeatureModel featureModel = adjustFeatureModel();

		createConfigurationFiles(featureModel);
	}

	/**
	 * The default implementation creates a new java-project in the field {@link #newProject}, opens it, and converts it to a FeatureIDE project.<br> <br> Can
	 * be overwritten by extending classes to accomodate {@link IComposerExtensionBase Composers} needs.
	 */
	protected void createProject() {
		newProject = SPLMigrationUtils.createProject(configurationData.projectName);

		openProjectHandleExceptions(newProject);

		convertToFeatureProject(configurationData);
	}

	private void openProjectHandleExceptions(IProject project) {
		assert (project != null) : INTERNAL_ASSERT_MESSAGE_PROJECT_IS_NULL;
		try {
			project.open(null);
		} catch (final CoreException e) {
			e.printStackTrace();
			CorePlugin.getDefault().logError(e);
		}
	}

	private void convertToFeatureProject(MigrationConfigurationData configurationData) {
		CorePlugin.setupFeatureProject(newProject, configurationData.composer.getId(), configurationData.sourcePath, configurationData.configPath,
				configurationData.buildPath, false, false, configurationData.composer.hasSourceFolder(), configurationData.composer.hasBuildFolder());

		CorePlugin.getDefault().addProject(newProject);
	}

	/**
	 * The default implementation recursively traverses the folders of the imported projects and copies all contents into a feature folder with the imported
	 * projects name in {@code newProject}. Can be overwritten by extending classes to accomodate {@link IComposerExtensionBase Composers} needs.
	 */
	protected void migrateProjects() {
		for (final IProject project : projects) {
			final IPath destinationPath = new Path(configurationData.sourcePath);

			assert newProject.getFolder(destinationPath).isAccessible() : DESTINATIONFOLDER_NOT_ACCESSIBLE_OR_WRONG_PATH;
			assert project.isOpen() : PROJECT + project.getName() + IS_NOT_OPEN_;

			final IPath featureFolderPath = SPLMigrationUtils.setupFolder(newProject.getFolder(destinationPath).getFolder(project.getName()));

			try {
				migrateClassPathDependentContent(project, featureFolderPath);
			} catch (final JavaModelException e) {
				e.printStackTrace();
			}

//			try
//			{
//				if(project.hasNature(ANDROID_NATURE))
//					copyProjectProperties(project, featureFolderPath);
//			} catch (CoreException e)
//			{
//				e.printStackTrace();
//			}
		}
	}

	@SuppressWarnings("unused")
	private void copyProjectProperties(IProject project, IPath destinationPath) {
		final IFile source = project.getFile(PROJECT_PROPERTIES_FILE_NAME);
		if (!source.exists()) {
			assert false : PROJECT_PROPERTIES_COULD_NOT_BE_COPIED_COMMA__BECAUSE_IT_DOES_NOT_EXIST_;
			return;
		}

		final IFile destination = newProject.getFile(destinationPath.makeRelativeTo(newProject.getFullPath()).append(PROJECT_PROPERTIES_FILE_NAME));
		if (!destination.exists()) {
			try {
				System.out.println("source: " + source + " ; target: " + destination);
				source.copy(destination.getFullPath(), true, null);
			} catch (final CoreException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 *
	 * @param project
	 * @param destinationPath
	 * @throws JavaModelException
	 */
	private void migrateClassPathDependentContent(IProject project, IPath destinationPath) throws JavaModelException {
		final JavaProject javaProjectToMigrate = new JavaProject(project, null);
		final JavaProject newJavaProject = new JavaProject(newProject, null);

		assert ((javaProjectToMigrate != null) && (newJavaProject != null)) : JAVA_PROJECTS_COULD_NOT_BE_CREATED;

		final IClasspathEntry[] classpathToMigrate = javaProjectToMigrate.getRawClasspath();
		final List<IClasspathEntry> newClassPath = new ArrayList<IClasspathEntry>();

		newClassPath.addAll(Arrays.asList(newJavaProject.getRawClasspath()));

		assert classpathToMigrate != null : CLASSPATH_OF_PROJECT_TO_MIGRATE_IS_NULL;

		migrateLibraryAndContainerEntries(newJavaProject, classpathToMigrate, newClassPath);
		migrateSourceFiles(project, destinationPath, classpathToMigrate);
		migrateProjectNatures(project);
	}

	/**
	 * @param project
	 */
	private void migrateProjectNatures(IProject project) {
		try {
			final List<String> natureIds = new ArrayList<String>();
			natureIds.addAll(Arrays.asList(newProject.getDescription().getNatureIds()));
			for (final String natureId : project.getDescription().getNatureIds()) {
				if (!natureIds.contains(natureId)) {
					natureIds.add(natureId);
				}
			}
			final IProjectDescription description = newProject.getDescription();
			description.setNatureIds(natureIds.toArray(new String[natureIds.size()]));
			newProject.setDescription(description, null);
		} catch (final CoreException e) {
			e.printStackTrace();
		}
	}

	/**
	 * @param project
	 * @param destinationPath
	 * @param classpathToMigrate
	 */
	private void migrateSourceFiles(IProject project, IPath destinationPath, IClasspathEntry[] classpathToMigrate) {
		final IPath relativeDestinationPath = ((IPath) destinationPath.clone()).makeRelativeTo(newProject.getFullPath());
		System.out.println("migrate source destination: " + destinationPath + " relative: " + relativeDestinationPath);
		final IFolder destination = newProject.getFolder(relativeDestinationPath);

		for (final IClasspathEntry entry : classpathToMigrate) {
			if (entry.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
				try {
					final IPath relativeSourcePath = entry.getPath().makeRelativeTo(project.getFullPath());
					final IFolder source = project.getFolder(relativeSourcePath);

					SPLMigrationUtils.recursiveCopyFiles(source, destination);

					newProject.refreshLocal(IResource.DEPTH_INFINITE, null);

				} catch (final CoreException e) {
					CorePlugin.getDefault().logError(e);
					e.printStackTrace();
				}
			}
		}
	}

	/**
	 * @param newJavaProject
	 * @param classpathToMigrate
	 * @param newClassPath
	 * @throws JavaModelException
	 */
	private void migrateLibraryAndContainerEntries(JavaProject newJavaProject, IClasspathEntry[] classpathToMigrate, List<IClasspathEntry> newClassPath)
			throws JavaModelException {
		for (final IClasspathEntry entry : classpathToMigrate) {
			if ((entry.getEntryKind() == IClasspathEntry.CPE_CONTAINER) || (entry.getEntryKind() == IClasspathEntry.CPE_LIBRARY)) {
				if (!newClassPath.contains(entry)) {
					newClassPath.add(entry);
				}
			}
		}
		newJavaProject.setRawClasspath(newClassPath.toArray(new IClasspathEntry[newClassPath.size()]), null);
	}

	/**
	 * The default implementation resets the featuremodel and creates a new one with an abstract "Base" feature that lists the migrated projects as alternative
	 * child features.<br> <br> The result is written to {@code /model.xml}. <br> <br> Can be overwritten by extending classes to accomodate
	 * {@link IComposerExtensionBase Composers} needs.
	 */
	protected IFeatureModel adjustFeatureModel() {
		final IFeatureModel featureModelOfVariants = generateFeatureModelOfVariants();
		SPLMigrationUtils.writeFeatureModelToDefaultFile(newProject, featureModelOfVariants);
		return featureModelOfVariants;
	}

	private IFeatureModel generateFeatureModelOfVariants() {
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(newProject);
		if (featureProject == null) {
			return null;
		}
		final IFeatureModel featureModel = featureProject.getFeatureModel();

		featureModel.reset();

		featureModel.getStructure().setRoot(FMFactoryManager.getFactory(featureModel).createFeature(featureModel, "Base").getStructure());
		featureModel.getStructure().getRoot().changeToAlternative();
		featureModel.getStructure().getRoot().setAbstract(true);

		for (final IProject project : projects) {
			featureModel.getStructure().getRoot()
					.addChild(FMFactoryManager.getFactory(featureModel).createFeature(featureModel, project.getName()).getStructure());
		}

		return featureModel;
	}

	/**
	 * The default implementation creates a .config file for each product variant and saves it to the user defined configpath. Can be overwritten by extending
	 * classes to accomodate {@link IComposerExtensionBase Composers} needs.
	 *
	 * @see SPLMigrationDialogSettingsPage#getConfigPath()
	 */
	protected void createConfigurationFiles(IFeatureModel featureModel) {
		for (final IProject project : projects) {
			try {
				SPLMigrationUtils.createConfigFile(featureModel, newProject, configurationData.configPath, project.getName());
			} catch (final UnsupportedEncodingException e) {
				CorePlugin.getDefault().logError(e);
				e.printStackTrace();
			} catch (final CoreException e) {
				CorePlugin.getDefault().logError(e);
				e.printStackTrace();
			}
		}
	}

	/**
	 * This default implementation gets instances and adapters for {@link IProject}s in the selection and adds them to the field {@code projects}. <br> <br>
	 *
	 * @param selection a selection that should contain {@link IProject}s
	 */
	protected void registerProjectsFromSelection(IStructuredSelection selection) {
		final SelectionWrapper<IProject> selectionWrapper = SelectionWrapper.init(selection, IProject.class);
		final Set<IProject> projects = new HashSet<IProject>();
		IProject curProject;
		while ((curProject = selectionWrapper.getNext()) != null) {
			projects.add(curProject);
		}
		registerProjectsForMigration(projects);
	}

}
