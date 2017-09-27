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

import static de.ovgu.featureide.fm.core.localization.StringTable.FUNCTIONALITY_NOT_YET_IMPLEMENTED;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;

import de.ovgu.featureide.ui.migration.wizard.SPLMigrationWizard;

/**
 * Handles the migration of products into a FeatureIDE project using the FeatureHouse composer.
 *
 * @author Konstantin Tonscheidt
 *
 */
public class VariantsToFeatureHouseSPLMigrator extends DefaultSPLMigrator {

	private WizardDialog dialog;

	public VariantsToFeatureHouseSPLMigrator(IStructuredSelection projectSelection) {
		this(true, projectSelection);
	}

	public VariantsToFeatureHouseSPLMigrator(boolean withGui, IStructuredSelection projectSelection) {
		registerProjectsFromSelection(projectSelection);

		if (withGui) {
			initWizard(projectSelection);
		} else {
			throw new IllegalArgumentException(FUNCTIONALITY_NOT_YET_IMPLEMENTED);
		}

	}

	private void initWizard(IStructuredSelection projectSelection) {
		dialog = new WizardDialog(null, new SPLMigrationWizard(this));
		dialog.open();
	}

}
