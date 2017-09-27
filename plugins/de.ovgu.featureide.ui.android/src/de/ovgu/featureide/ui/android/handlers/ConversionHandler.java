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
package de.ovgu.featureide.ui.android.handlers;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;

import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;
import de.ovgu.featureide.ui.android.wizards.ConversionWizard;

/**
 * Starts the conversion wizard.
 *
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
 */
public class ConversionHandler extends ASelectionHandler {

	@Override
	protected boolean startAction(IStructuredSelection selection) {
		final ConversionWizard wizard = new ConversionWizard();
		wizard.init(null, selection);
		new WizardDialog(null, wizard).open();
		return false;
	}

	@Override
	protected void singleAction(Object element) {}

}
