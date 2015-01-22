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
package de.ovgu.featureide.ui.variantimport.wizard;

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
