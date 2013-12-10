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
package de.ovgu.featureide.core.mspl.popup.actions;

import java.util.Iterator;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.core.mspl.wizard.NewInterfaceWizard;

public class NewInterfaceAction implements IObjectActionDelegate {

	private IWorkbenchPart workbenchPart;

	public NewInterfaceAction() {
		super();
	}

	@Override
	public void run(IAction action) {
		ISelection selection = workbenchPart.getSite().getSelectionProvider()
				.getSelection();

		if (selection instanceof IStructuredSelection) {
			IStructuredSelection structuredSelection = (IStructuredSelection) selection;

			for (Iterator<?> iter = structuredSelection.iterator(); iter
					.hasNext();) {
				Object obj = iter.next();

				if (obj instanceof IAdaptable) {
					IProject project = (IProject) ((IAdaptable) obj)
							.getAdapter(IProject.class);

					if (project != null) {
						WizardDialog wizardDialog = new WizardDialog(
								workbenchPart.getSite().getShell(),
								new NewInterfaceWizard());

						if (wizardDialog.open() == Window.OK) {
							System.out.println("Ok pressed");
						} else {
							System.out.println("Cancel pressed");
						}
					}
				}
			}
		}
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
	}

	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		workbenchPart = targetPart;
	}

}
