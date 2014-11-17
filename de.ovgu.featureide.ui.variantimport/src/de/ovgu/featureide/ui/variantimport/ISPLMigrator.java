package de.ovgu.featureide.ui.variantimport;

import java.util.Set;

import org.eclipse.core.resources.IProject;

/**
 * Interface for Migration of multiple projects into a FeatureIDE-project. It is
 * highly recommended to extend the default implementation
 * {@link DefaultSPLMigrator}.
 * 
 * 
 * @author Konstantin Tonscheidt
 * 
 */
public interface ISPLMigrator
{
	/**
	 * Registers the Projects that should be migrated with the Migrator.
	 * 
	 * @see DefaultSPLMigrator#registerProjectsFromSelection(org.eclipse.jface.viewers.IStructuredSelection)
	 * 
	 * @param projects
	 */
	public abstract void registerProjectsForMigration(Set<IProject> projects);

	/**
	 * Migrates previously registered projects into a new FeautureIDE-project.
	 * 
	 * @param configurationData
	 *            should contain metadata for creation of the new project.
	 * 
	 * @see DefaultSPLMigrator#migrate(MigrationConfigurationData)
	 * @see #registerProjectsForMigration(Set)
	 */
	public abstract void migrate(MigrationConfigurationData configurationData);

}