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
package de.ovgu.featureide.core.conversion.ahead_featurehouse.handlers;

import static de.ovgu.featureide.fm.core.localization.StringTable.COMPOSER_CONVERSION;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE_FILES_WILL_BE_CHANGED_AUTOMATICALLY__FEATUREHOUSE_SUPPORS_JAVA_5_AND_AHEAD_JAVA_4_COMMA__THIS_CAN_CAUSE_PROBLEMS_DURING_CONVERION__YOU_SHOULD_HAVE_A_COPY_OF_THIS_PROJECT_;

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
		return MessageDialog.open(MessageDialog.WARNING, PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), COMPOSER_CONVERSION,
				SOURCE_FILES_WILL_BE_CHANGED_AUTOMATICALLY__FEATUREHOUSE_SUPPORS_JAVA_5_AND_AHEAD_JAVA_4_COMMA__THIS_CAN_CAUSE_PROBLEMS_DURING_CONVERION__YOU_SHOULD_HAVE_A_COPY_OF_THIS_PROJECT_,
				SWT.NONE);
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
