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
package de.ovgu.featureide.ui.migration.wizard;

import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_PRODUCTS_INTO_A_SIMPLE_SOFTWARE_PRODUCT_LINE;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.migration.impl.ISPLMigrator;
import de.ovgu.featureide.migration.impl.MigrationConfigurationData;
import de.ovgu.featureide.ui.migration.plugin.SPLMigrationCommandHandler;
import de.ovgu.featureide.ui.migration.plugin.SPLMigrationPlugin;

/**
 * This class implements most of the {@link SPLMigrationPlugin}s functionality. It is invoked by the {@link SPLMigrationCommandHandler}. The
 * {@link WizardDialog} consists of two pages: {@link SPLMigrationDialogNamePage} and {@link SPLMigrationDialogSettingsPage} .
 *
 * @see {@link #performFinish()}
 *
 * @author Konstantin Tonscheidt
 *
 */
public class SPLMigrationWizard extends Wizard implements INewWizard {

	private SPLMigrationDialogNamePage namePage;
	private SPLMigrationDialogSettingsPage projectPage;

	private final ISPLMigrator migrator;

	public SPLMigrationWizard(ISPLMigrator migrator) {
		this.migrator = migrator;
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		// not necessary
	}

	@Override
	public void addPages() {
		setWindowTitle(IMPORT_PRODUCTS_INTO_A_SIMPLE_SOFTWARE_PRODUCT_LINE);

		namePage = new SPLMigrationDialogNamePage();
		projectPage = new SPLMigrationDialogSettingsPage();

		addPage(namePage);
		addPage(projectPage);
	}

	/**
	 * Delegates the actual creation of the SPL from the {@link IProject}s contained in {@code projects}
	 */
	@Override
	public boolean performFinish() {
		final MigrationConfigurationData configurationData = new MigrationConfigurationData(namePage.getProjectName(), projectPage.getCompositionTool(),
				projectPage.getSourcePath(), projectPage.getConfigPath(), projectPage.getBuildPath());

		migrator.migrate(configurationData);

		return true;
	}

}
