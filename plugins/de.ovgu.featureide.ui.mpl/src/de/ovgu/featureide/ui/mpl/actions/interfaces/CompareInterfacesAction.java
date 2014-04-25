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
package de.ovgu.featureide.ui.mpl.actions.interfaces;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.ui.mpl.actions.AProjectJobAction;
import de.ovgu.featureide.ui.mpl.wizards.FeatureInterfaceWizard;
import de.ovgu.featureide.ui.mpl.wizards.WizardConstants;

/**
 * Action to compare all possible interface from the current configuration.
 * 
 * @author Sebastian Krieter
 */
public class CompareInterfacesAction extends AProjectJobAction {
	private FeatureInterfaceWizard wizard;

	@Override
	protected boolean startAction() {
		wizard = new FeatureInterfaceWizard("Compare Configuration Interfaces");
		WizardDialog dialog = new WizardDialog(Display.getCurrent().getActiveShell(), wizard);
		return dialog.open() == Dialog.OK;
	}
	
	@Override
	protected void endAction() {
		MPLPlugin.getDefault().compareConfigurationInterfaces(
				projects, 
				(String) wizard.getData(WizardConstants.KEY_VIEWNAME), 
				(Integer) wizard.getData(WizardConstants.KEY_VIEWLEVEL), 
				(Integer) wizard.getData(WizardConstants.KEY_CONFIGLIMIT));
	}

}
