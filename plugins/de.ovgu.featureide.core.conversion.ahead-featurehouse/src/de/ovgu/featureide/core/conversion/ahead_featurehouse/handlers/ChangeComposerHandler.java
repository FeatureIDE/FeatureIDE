/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.conversion.ahead_featurehouse.handlers;

import static de.ovgu.featureide.fm.core.localization.StringTable.COMPOSER_CONVERSION;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATUREHOUSE_SUPPORTS_JAVA_5_AND_AHEAD_JAVA_4;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.ahead.AheadComposer;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.conversion.ahead_featurehouse.actions.AHEADToFeatureHouseConversion;
import de.ovgu.featureide.core.conversion.ahead_featurehouse.actions.FeatureHouseToAHEADConversion;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.ui.handlers.base.AFeatureProjectHandler;

/**
 *
 * A action to replace the composer of a given project.
 *
 * @author Jens Meinicke
 * @author Sebastian Krieter
 */
public class ChangeComposerHandler extends AFeatureProjectHandler {

	@Override
	protected boolean startAction(IStructuredSelection selection) {
		return MessageDialog.open(MessageDialog.CONFIRM, PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), COMPOSER_CONVERSION,
				FEATUREHOUSE_SUPPORTS_JAVA_5_AND_AHEAD_JAVA_4, SWT.NONE);
	}

	@Override
	protected void singleAction(IFeatureProject featureProject) {
		if (AheadComposer.COMPOSER_ID.equals(featureProject.getComposerID())) {
			new AHEADToFeatureHouseConversion(featureProject);
		} else if (FeatureHouseComposer.COMPOSER_ID.equals(featureProject.getComposerID())) {
			new FeatureHouseToAHEADConversion(featureProject);
		}
	}

}
