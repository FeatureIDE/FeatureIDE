package de.ovgu.featureide.ui.variantimport;

import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.ui.wizards.NewFeatureProjectPage;

/**
 * Second Page of the {@link SPLMigrationWizard}. Enables the user to choose the
 * new projects composer, and the pathes for source, feature and config folders.
 * 
 * 
 * @author Konstantin Tonscheidt
 * 
 */
public class SPLMigrationDialogSettingsPage extends NewFeatureProjectPage
{

	public SPLMigrationDialogSettingsPage()
	{
		super();
		setDescription("Import products into a simple Software Product Line");
	}

	@Override
	public boolean canFlipToNextPage()
	{
		return false;
	}
	
	@Override
	public void createControl(Composite parent)
	{
		super.createControl(parent);
		
		validateComposerMigrationSupport();
	}
	
	@Override
	protected void dialogChanged()
	{
		super.dialogChanged();
		
		validateComposerMigrationSupport();
	}

	/**
	 * Only allow finishing, when the composer is supported by the MigrationPlugin
	 */
	private void validateComposerMigrationSupport()
	{
		final boolean composerSupported = getCompositionTool().supportsMigration();
		
		if(!composerSupported)
			updateStatus("Migration is currently not supported for the selected Composer. Please choose another one");
		else
			setErrorMessage(null);
		
		setPageComplete(isPageComplete() && composerSupported);
	}
}
