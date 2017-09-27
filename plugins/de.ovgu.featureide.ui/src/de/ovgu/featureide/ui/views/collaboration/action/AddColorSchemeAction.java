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
package de.ovgu.featureide.ui.views.collaboration.action;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.wizards.NewColorSchemeWizard;

/**
 * Action to add an colorscheme
 *
 * @author Sebastian Krieter
 */
public class AddColorSchemeAction extends AbstractColorAction {

	public AddColorSchemeAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView) {
		super(text, view, collaborationView, 0);
		setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD));
	}

	@Override
	protected boolean action(IFeatureModel fm, String collName) {
		final NewColorSchemeWizard wizard = new NewColorSchemeWizard(fm, collaborationView);

		final WizardDialog dialog = new WizardDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), wizard);
		dialog.create();
		dialog.open();

		return false;
	}

}
