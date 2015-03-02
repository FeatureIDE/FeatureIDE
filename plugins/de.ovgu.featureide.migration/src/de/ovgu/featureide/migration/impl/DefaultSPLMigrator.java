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
package de.ovgu.featureide.migration.impl;

import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.migration.wizard.SPLMigrationDialogSettingsPage;

@SuppressWarnings("restriction")
public abstract class DefaultSPLMigrator implements ISPLMigrator
{
	public static final String PROJECT_PROPERTIES_FILE_NAME = "project.properties";
	public static final String DEFAULT_PROJECT_NAME = "migratedSPL";
	public static final String ANDROID_NATURE = "com.android.ide.eclipse.adt.AndroidNature";

	/**
	 * The new project which contains the software product line, when the
	 * migration is done.
	 */
	protected IProject newProject;

	/**
	 * The (Java) projects which are going to be migrated into a SPL.
	 */
	protected Set<IProject> projects;

	protected MigrationConfigurationData configurationData;

	public DefaultSPLMigrator()
	{
		super();
	}

	@Override
	public void registerProjectsForMigration(Set<IProject> projects)
	{
		if (projects == null || projects.isEmpty())
			throw new IllegalArgumentException("No projects were selected for Migration");

		this.projects = projects;
	}

	@Override
	public void migrate(MigrationConfigurationData configurationData)
	{
		this.configurationData = configurationData;

		createProject();

		migrateProjects();

		adjustFeatureModel();

		createConfigurationFiles();
	}

	/**
	 * The default implementation creates a new java-project in the field
	 * {@link #newProject}, opens it, and converts it to a FeatureIDE project.<br>
	 * <br>
	 * Can be overwritten by extending classes to accomodate
	 * {@link IComposerExtensionBase Composers} needs.
	 */
	protected void createProject()
	{
		newProject = SPLMigrationUtils.createProject(configurationData.projectName);

		openProjectHandleExceptions(newProject);

		convertToFeatureProject(configurationData);
	}

	private void openProjectHandleExceptions(IProject project)
	{
		assert (project != null) : "Tried to open null project.";
		try
		{
			project.open(null);
		} catch (CoreException e)
		{
			e.printStackTrace();
			CorePlugin.getDefault().logError(e);
		}
	}

	private void convertToFeatureProject(MigrationConfigurationData configurationData)
	{
		CorePlugin.setupFeatureProject(newProject, configurationData.composer.getId(),
				configurationData.sourcePath, configurationData.configPath,
				configurationData.buildPath, false);

		CorePlugin.getDefault().addProject(newProject);
	}

	/**
	 * The default implementation recursively traverses the folders of the
	 * imported projects and copies all contents into a feature folder with the
	 * imported projects name in {@code newProject}. Can be overwritten by
	 * extending classes to accomodate {@link IComposerExtensionBase Composers}
	 * needs.
	 */
	protected void migrateProjects()
	{
		for (IProject project : projects)
		{
			IPath destinationPath = new Path(configurationData.sourcePath);

			assert newProject.getFolder(destinationPath).isAccessible() : "Destinationfolder not accessible or wrong path";
			assert project.isOpen() : "Project " + project.getName() + " is not open.";

			IPath featureFolderPath = SPLMigrationUtils.setupFolder(newProject.getFolder(destinationPath)
					.getFolder(project.getName()));

			try
			{
				migrateClassPathDependentContent(project, featureFolderPath);
			} catch (JavaModelException e)
			{
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

	private void copyProjectProperties(IProject project, IPath destinationPath)
	{
		final IFile source = project.getFile(PROJECT_PROPERTIES_FILE_NAME);
		if(!source.exists())
		{
			assert false : "project.properties could not be copied, because it does not exist.";
			return;
		}
		
		final IFile destination = newProject.getFile(destinationPath.makeRelativeTo(newProject.getFullPath()).append(PROJECT_PROPERTIES_FILE_NAME));
		if (!destination.exists())
			try
			{
				System.out.println("source: " + source + " ; target: " + destination);
				source.copy(destination.getFullPath(), true, null);
			} catch (CoreException e)
			{
				e.printStackTrace();
			}
	}

	/**
	 * 
	 * @param project
	 * @param destinationPath
	 * @throws JavaModelException
	 */
	private void migrateClassPathDependentContent(IProject project, IPath destinationPath)
			throws JavaModelException
	{
		JavaProject javaProjectToMigrate = new JavaProject(project, null);
		JavaProject newJavaProject = new JavaProject(newProject, null);

		assert (javaProjectToMigrate != null && newJavaProject != null) : "Java Projects could not be created";

		IClasspathEntry[] classpathToMigrate = javaProjectToMigrate.getRawClasspath();
		List<IClasspathEntry> newClassPath = new ArrayList<IClasspathEntry>();

		newClassPath.addAll(Arrays.asList(newJavaProject.getRawClasspath()));

		assert classpathToMigrate != null : "classPath of project to migrate is null";

		migrateLibraryAndContainerEntries(newJavaProject, classpathToMigrate, newClassPath);
		migrateSourceFiles(project, destinationPath, classpathToMigrate);
		migrateProjectNatures(project);
	}

	/**
	 * @param project
	 */
	private void migrateProjectNatures(IProject project)
	{
		try
		{
			List<String> natureIds = new ArrayList<String>();
			natureIds.addAll(Arrays.asList(newProject.getDescription().getNatureIds()));
			for(String natureId : project.getDescription().getNatureIds()){
				if(!natureIds.contains(natureId))
					natureIds.add(natureId);
			}
			IProjectDescription description = newProject.getDescription();
			description.setNatureIds(natureIds.toArray(new String[natureIds.size()]));
			newProject.setDescription(description, null);
		} catch (CoreException e)
		{
			e.printStackTrace();
		}
	}

	/**
	 * @param project
	 * @param destinationPath
	 * @param classpathToMigrate
	 */
	private void migrateSourceFiles(IProject project, IPath destinationPath,
			IClasspathEntry[] classpathToMigrate)
	{
		IPath relativeDestinationPath = ((IPath) destinationPath.clone()).makeRelativeTo(newProject.getFullPath());
		System.out.println("migrate source destination: " + destinationPath + " relative: "+ relativeDestinationPath );
		IFolder destination = newProject.getFolder(relativeDestinationPath);
		
		for (IClasspathEntry entry : classpathToMigrate)
		{
			if (entry.getEntryKind() == IClasspathEntry.CPE_SOURCE)
			{
				try
				{
					IPath relativeSourcePath = entry.getPath().makeRelativeTo(project.getFullPath());
					IFolder source = project.getFolder(relativeSourcePath);
					
					SPLMigrationUtils.recursiveCopyFiles(source, destination);
					
					newProject.refreshLocal(IProject.DEPTH_INFINITE, null);
					
				} catch (CoreException e)
				{
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
	private void migrateLibraryAndContainerEntries(JavaProject newJavaProject,
			IClasspathEntry[] classpathToMigrate, List<IClasspathEntry> newClassPath)
			throws JavaModelException
	{
		for (IClasspathEntry entry : classpathToMigrate)
		{
			if (entry.getEntryKind() == IClasspathEntry.CPE_CONTAINER
					|| entry.getEntryKind() == IClasspathEntry.CPE_LIBRARY)
				if (!newClassPath.contains(entry))
					newClassPath.add(entry);
		}
		newJavaProject.setRawClasspath(
				newClassPath.toArray(new IClasspathEntry[newClassPath.size()]), null);
	}

	/**
	 * The default implementation resets the featuremodel and creates a new one
	 * with an abstract "Base" feature that lists the migrated projects as
	 * alternative child features.<br>
	 * <br>
	 * The result is written to {@code /model.xml}. <br>
	 * <br>
	 * Can be overwritten by extending classes to accomodate
	 * {@link IComposerExtensionBase Composers} needs.
	 */
	protected void adjustFeatureModel()
	{
		final FeatureModel featureModelOfVariants = generateFeatureModelOfVariants();

		SPLMigrationUtils.writeFeatureModelToDefaultFile(newProject, featureModelOfVariants);
	}

	private FeatureModel generateFeatureModelOfVariants()
	{
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(newProject);
		final FeatureModel featureModel = featureProject.getFeatureModel();

		featureModel.reset();

		featureModel.setRoot(new Feature(featureModel, "Base"));
		featureModel.getRoot().changeToAlternative();
		featureModel.getRoot().setAbstract(true);

		for (IProject project : projects)
			featureModel.getRoot().addChild(new Feature(featureModel, project.getName()));

		return featureModel;
	}

	/**
	 * The default implementation creates a .config file for each product
	 * variant and saves it to the user defined configpath. Can be overwritten
	 * by extending classes to accomodate {@link IComposerExtensionBase
	 * Composers} needs.
	 * 
	 * @see SPLMigrationDialogSettingsPage#getConfigPath()
	 */
	protected void createConfigurationFiles()
	{
		for (IProject project : projects)
			try
			{
				SPLMigrationUtils.createConfigFile(newProject, configurationData.configPath,
						project.getName());
			} catch (UnsupportedEncodingException e)
			{
				CorePlugin.getDefault().logError(e);
				e.printStackTrace();
			} catch (CoreException e)
			{
				CorePlugin.getDefault().logError(e);
				e.printStackTrace();
			}
	}

	/**
	 * This default implementation gets instances and adapters for
	 * {@link IProject}s in the selection and adds them to the field
	 * {@code projects}. <br>
	 * <br>
	 * 
	 * @param selection
	 *            a selection that should contain {@link IProject}s
	 */
	protected void registerProjectsFromSelection(IStructuredSelection selection)
	{
		Set<IProject> projects = new HashSet<IProject>();
		Iterator<?> iterator = selection.iterator();
		while (iterator.hasNext())
		{
			Object selectedObject = iterator.next();
			IProject project = null;

			if (selectedObject instanceof IProject)
				project = (IProject) selectedObject;
			else
				if (selectedObject instanceof IAdaptable)
					project = (IProject) ((IAdaptable) selectedObject).getAdapter(IProject.class);

			assert (!projects.contains(project)) : "Found two equal projects in selection";

			if (project != null)
				projects.add(project);
		}
		registerProjectsForMigration(projects);
	}

}
