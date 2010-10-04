/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.ahead.views.collaboration.action;


import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;

import de.ovgu.featureide.ui.ahead.AheadUIPlugin;
import de.ovgu.featureide.ui.ahead.wizards.NewJakFileWizard;
import de.ovgu.featureide.ui.views.collaboration.action.IRunAddRoleAction;

/**
 * Opens the NewJakFileWizard at CollaborationView
 * 
 * @author Jens Meinicke
 */
public class RunAddRoleActionAHEAD implements IRunAddRoleAction{
	
	@Override
	public void run(GraphicalViewerImpl viewer, IStructuredSelection selection) {
		NewJakFileWizard wiz = new NewJakFileWizard();
		wiz.init(AheadUIPlugin.getDefault().getWorkbench(), null);
		WizardDialog dialog = new WizardDialog(wiz.getShell(),wiz);
		dialog.open();
	}
}
