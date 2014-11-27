package de.ovgu.featureide.ui.variantimport;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

/**
 * This class implements most of the {@link SPLMigrationPlugin}s functionality.
 * It is invoked by the {@link SPLMigrationCommandHandler}. The
 * {@link WizardDialog} consists of two pages:
 * {@link SPLMigrationDialogNamePage} and {@link SPLMigrationDialogSettingsPage}
 * .
 * 
 * @see {@link #performFinish()}
 * 
 * @author Konstantin Tonscheidt
 * 
 */
public class SPLMigrationWizard extends Wizard implements INewWizard
{
	private SPLMigrationDialogNamePage namePage;
	private SPLMigrationDialogSettingsPage projectPage;

	private ISPLMigrator migrator;

	public SPLMigrationWizard(ISPLMigrator migrator)
	{
		this.migrator = migrator;
	}
	
	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection)
	{
		//not necessary
	}

	@Override
	public void addPages()
	{
		setWindowTitle("Import products into a simple Software Product Line");

		namePage = new SPLMigrationDialogNamePage();
		projectPage = new SPLMigrationDialogSettingsPage();

		addPage(namePage);
		addPage(projectPage);
	}

	/**
	 * Delegates the actual creation of the SPL from the {@link IProject}s
	 * contained in {@code projects}
	 */
	@Override
	public boolean performFinish()
	{
		MigrationConfigurationData configurationData = new MigrationConfigurationData(
				namePage.getProjectName(), projectPage.getCompositionTool(),
				projectPage.getSourcePath(), projectPage.getConfigPath(),
				projectPage.getBuildPath());
		
		migrator.migrate(configurationData);

		return true;
	}

}
