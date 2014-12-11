package de.ovgu.featureide.ui.variantimport.migration;

import java.io.UnsupportedEncodingException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.variantimport.wizard.SPLMigrationDialogSettingsPage;

public abstract class DefaultSPLMigrator implements ISPLMigrator
{
	public static final String DEFAULT_PROJECT_NAME = "migratedSPL";

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

		createFeatureProject();

		copyImportedProjectsCodeIntoFeatureFolders();

		adjustFeatureModel();

		createConfigFiles();
	}

	/**
	 * The default implementation creates a new java-project in the field
	 * {@link #newProject}, opens it, and converts it to a FeatureIDE project.<br>
	 * <br>
	 * Can be overwritten by extending classes to accomodate
	 * {@link IComposerExtensionBase Composers} needs.
	 */
	protected void createFeatureProject()
	{
		createNewProject(configurationData.projectName);

		openProjectHandleExceptions(newProject);

		convertToFeatureProject(configurationData);
	}

	private void createNewProject(String projectName)
	{
		newProject = SPLMigrationUtils.createProject(projectName);
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
	protected void copyImportedProjectsCodeIntoFeatureFolders()
	{
		for (IProject project : projects)
		{
			IPath destinationPath = new Path(configurationData.sourcePath);
			IPath sourcePath = new Path(project.getName());

			assert newProject.getFolder(destinationPath).isAccessible() : "Destinationfolder not accessible or wrong path";
			assert project.isOpen() : "Project " + project.getName() + " is not open.";

			try
			{
				IFolder sourceFolder = newProject.getFolder(destinationPath).getFolder(sourcePath);
				if (sourceFolder.exists())
				{
					sourceFolder.delete(true, null);
				}
				sourceFolder.create(true, true, null);
				SPLMigrationUtils.recursiveCopyFiles(project, sourceFolder);
				newProject.refreshLocal(IProject.DEPTH_INFINITE, null);
			} catch (CoreException e)
			{
				CorePlugin.getDefault().logError(e);
				e.printStackTrace();
			}
		}
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
	protected void createConfigFiles()
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
			
			if(project!=null)
			projects.add(project);
		}
		registerProjectsForMigration(projects);
	}

}