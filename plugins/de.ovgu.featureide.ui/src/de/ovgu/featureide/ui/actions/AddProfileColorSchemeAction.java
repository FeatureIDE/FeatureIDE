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
package de.ovgu.featureide.ui.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.ui.wizards.NewColorSchemeWizard;

/**
 * This Class contains one of the three actions, which is added to the menu
 *
 * The other related classes are:
 *
 * @see de.ovgu.featureide.ui.actions.DeleteProfileColorScheme.java
 * @see de.ovgu.featureide.ui.actions.RenameProfileColorScheme.java
 *
 * @author Jonas Weigt
 * @author Christian Harnisch
 * @author Marcus Pinnecke
 */
public class AddProfileColorSchemeAction extends Action {

	private final IFeatureModel model;

	/*
	 * Constructor
	 */
	public AddProfileColorSchemeAction(String text, IFeatureModel model) {
		super(text);
		this.model = model;
		setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD));
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run() this Method calls the Wizard and saves the configuration
	 */
	@Override
	public void run() {
		final NewColorSchemeWizard wizard = new NewColorSchemeWizard(model, null);

		final WizardDialog dialog = new WizardDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), wizard);
		dialog.create();
		dialog.open();

	}

}
