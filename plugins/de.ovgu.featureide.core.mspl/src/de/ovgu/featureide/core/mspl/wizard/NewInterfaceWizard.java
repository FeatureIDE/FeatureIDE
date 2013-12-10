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
package de.ovgu.featureide.core.mspl.wizard;

import org.eclipse.jface.wizard.Wizard;

public class NewInterfaceWizard extends Wizard {

	protected SelectProjectWizardPage selectProject;
	protected SelectFeaturesWizardPage selectFeatures;

	@Override
	public void addPages() {
		selectProject = new SelectProjectWizardPage();
		addPage(selectProject);
		selectFeatures = new SelectFeaturesWizardPage(selectProject);
		addPage(selectFeatures);
	}

	@Override
	public boolean performFinish() {
		// TODO: generate interface
		return false;
	}

}
