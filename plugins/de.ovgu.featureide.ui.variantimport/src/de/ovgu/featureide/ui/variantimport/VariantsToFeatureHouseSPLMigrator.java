package de.ovgu.featureide.ui.variantimport;

import java.io.UnsupportedEncodingException;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;

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
