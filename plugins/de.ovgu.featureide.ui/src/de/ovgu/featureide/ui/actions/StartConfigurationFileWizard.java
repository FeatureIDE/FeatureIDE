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
package de.ovgu.featureide.ui.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

import de.ovgu.featureide.ui.wizards.NewConfigurationFileWizard;

/**
 * Starts the configuration file wizard for the selected configuration file
 * at the context menu. 
 */
public class StartConfigurationFileWizard implements IWorkbenchWindowActionDelegate {

	private IWorkbenchWindow window;

	public void dispose() {
	}

	public void init(IWorkbenchWindow window) {
		this.window=window;
	}

	public void run(IAction action) {
		
		NewConfigurationFileWizard wizard=new NewConfigurationFileWizard();
		ISelection selection = window.getSelectionService().getSelection();
		
		if(selection instanceof IStructuredSelection){
			wizard.init(window.getWorkbench(), (IStructuredSelection) selection);	
		}
		else{
			wizard.init(window.getWorkbench(), null);
		}
		
		WizardDialog dialog = new WizardDialog(window.getShell(), wizard);
		dialog.open();
	}

	public void selectionChanged(IAction action, ISelection selection) {
	}

}
