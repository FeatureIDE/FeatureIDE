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
package de.ovgu.featureide.ui.views.collaboration.action;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.editparts.ClassEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.wizards.NewFeatureIDEFileWizard;

/**
 * Add a role to the CollaborationDiagramm.
 * 
 * @author Constanze Adler
 * @author Stephan Besecke
 * @author Jens Meinicke
 */
public class AddRoleAction extends Action {
	private GraphicalViewerImpl viewer;

	protected IStructuredSelection selection;

	public AddRoleAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView) {
		super(text);
		viewer = view;
	}

	public void setEnabled(boolean enable) {
		selection = (IStructuredSelection)viewer.getSelection();
		super.setEnabled(true);
	}

	public void run() {
		IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		String feature = "";
		String clss = "";
		Object selectedItem = selection.getFirstElement();

		if (selectedItem != null){
			if (selectedItem instanceof CollaborationEditPart) {
				feature = ((CollaborationEditPart) selectedItem).getCollaborationModel().getName();
			}

			else if (selectedItem instanceof ClassEditPart) {
				clss = ((ClassEditPart) selectedItem).getClassModel().getName();
				if (clss.contains("."))
					clss = clss.substring(0,clss.lastIndexOf("."));
			}
		}
		
		NewFeatureIDEFileWizard wizard = new NewFeatureIDEFileWizard();
		wizard.init(PlatformUI.getWorkbench(), (IStructuredSelection)selection, feature, clss);

		WizardDialog dialog = new WizardDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), wizard);
		dialog.create();
		dialog.open();

	}
}
