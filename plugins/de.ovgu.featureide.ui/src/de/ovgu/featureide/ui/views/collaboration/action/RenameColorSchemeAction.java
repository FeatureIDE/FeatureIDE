/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.views.collaboration.action;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.wizards.RenameColorSchemeWizard;

/**
 * Action to rename a colorscheme
 * 
 * @author Sebastian Krieter
 */
public class RenameColorSchemeAction extends AbstractColorAction {
	
	public RenameColorSchemeAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView) {
		super(text, view, collaborationView, 0);
		setImageDescriptor(PlatformUI.getWorkbench().getSharedImages()
				.getImageDescriptor(ISharedImages.IMG_ETOOL_CLEAR));
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.collaboration.color.action.AbstractColorAction#action(de.ovgu.featureide.fm.core.Feature)
	 */
	@Override
	protected boolean action(FeatureModel fm, String collName) {
		RenameColorSchemeWizard wizard = new RenameColorSchemeWizard(fm);

		WizardDialog dialog = new WizardDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), wizard);
		dialog.create();
		dialog.open();
		
		return false;
	}
}
