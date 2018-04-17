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
package de.ovgu.featureide.ui.migration.plugin;

import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;
import de.ovgu.featureide.migration.impl.VariantsToFeatureHouseSPLMigrator;
import de.ovgu.featureide.ui.migration.wizard.SPLMigrationWizard;

/**
 * This class handles the {@code SPLMigrationCommand} which is triggered by the context menu on a selection of projects in the eclipse packet manager. Most of
 * the Implementation is handled by the {@link SPLMigrationWizard}.
 *
 * @author Konstantin Tonscheidt
 *
 */
public class SPLMigrationCommandHandler extends ASelectionHandler {

	@Override
	protected boolean startAction(IStructuredSelection selection) {
		new VariantsToFeatureHouseSPLMigrator(selection);
		return false;
	}

	@Override
	protected void singleAction(Object element) {}

}
