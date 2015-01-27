package de.ovgu.featureide.ui.variantimport.migration;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;

import de.ovgu.featureide.ui.variantimport.wizard.SPLMigrationWizard;

/**
 * Handles the migration of products into a FeatureIDE project using the
 * FeatureHouse composer.
 * 
 * @author Konstantin Tonscheidt
 * 
 */
public class VariantsToFeatureHouseSPLMigrator extends DefaultSPLMigrator
{
	private WizardDialog dialog;

	public VariantsToFeatureHouseSPLMigrator(IStructuredSelection projectSelection)
	{
		this(true, projectSelection);
	}

	public VariantsToFeatureHouseSPLMigrator(boolean withGui, IStructuredSelection projectSelection)
	{
		registerProjectsFromSelection(projectSelection);

		if (withGui)
			initWizard(projectSelection);
		else
			throw new IllegalArgumentException("Functionality not yet implemented");

	}

	private void initWizard(IStructuredSelection projectSelection)
	{
		dialog = new WizardDialog(null, new SPLMigrationWizard(this));
		dialog.open();
	}

}
