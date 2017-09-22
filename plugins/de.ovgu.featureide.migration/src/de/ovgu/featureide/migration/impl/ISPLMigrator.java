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

import java.util.Set;

import org.eclipse.core.resources.IProject;

/**
 * Interface for Migration of multiple projects into a FeatureIDE-project. It is highly recommended to extend the default implementation
 * {@link DefaultSPLMigrator}.
 *
 *
 * @author Konstantin Tonscheidt
 *
 */
public interface ISPLMigrator {

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
	 * @param configurationData should contain metadata for creation of the new project.
	 *
	 * @see DefaultSPLMigrator#migrate(MigrationConfigurationData)
	 * @see #registerProjectsForMigration(Set)
	 */
	public abstract void migrate(MigrationConfigurationData configurationData);

}
