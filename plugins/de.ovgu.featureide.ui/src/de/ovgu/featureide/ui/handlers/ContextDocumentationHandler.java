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
package de.ovgu.featureide.ui.handlers;

import static de.ovgu.featureide.fm.core.localization.StringTable.CONTEXTDOCUMENTATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.DOCUMENTATION_WIZARD;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.ui.handlers.base.AProjectJobHandler;
import de.ovgu.featureide.fm.ui.wizards.AbstractWizard;
import de.ovgu.featureide.fm.ui.wizards.WizardConstants;
import de.ovgu.featureide.ui.wizards.BuildDocWizard;

public class ContextDocumentationHandler extends AProjectJobHandler {

	@Override
	protected AbstractWizard instantiateWizard() {
		return new BuildDocWizard(DOCUMENTATION_WIZARD, CONTEXTDOCUMENTATION, true);
	}

	@Override
	protected void endAction() {
		CorePlugin.getDefault().buildContextDocumentation(projects, (String) wizard.getData(WizardConstants.KEY_OUT_DOCOPTIONS),
				(String) wizard.getData(WizardConstants.KEY_OUT_FEATURE));
	}

}
