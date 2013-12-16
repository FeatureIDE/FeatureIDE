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

import java.io.ByteArrayInputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.wizard.Wizard;

import de.ovgu.featureide.core.mspl.InterfaceProject;
import de.ovgu.featureide.core.mspl.MSPLPlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.velvet.VelvetFeatureModelWriter;

public class NewInterfaceWizard extends Wizard {

	protected SelectProjectWizardPage selectProject;
	protected SelectFeaturesWizardPage selectFeatures;

	protected IProject project;

	public NewInterfaceWizard(IProject project) {
		super();
		this.project = project;
	}

	@Override
	public void addPages() {
		selectProject = new SelectProjectWizardPage();
		addPage(selectProject);
		selectFeatures = new SelectFeaturesWizardPage(selectProject);
		addPage(selectFeatures);
	}

	@Override
	public boolean performFinish() {
		FeatureModel fm = selectFeatures.createFeatureModel();

		VelvetFeatureModelWriter modelWriter = new VelvetFeatureModelWriter(fm,
				true);
		String interfaceContent = modelWriter.writeToString();

		ByteArrayInputStream interfaceContentStream = new ByteArrayInputStream(
				interfaceContent.getBytes());

		try {
			IFolder mplFolder = project.getFolder("MPL");
			if (!mplFolder.exists())
				mplFolder.create(true, true, null);

			IFile interfaceFile = mplFolder.getFile(fm.getRoot().getName()
					+ ".velvet");

			if (!mplFolder.exists())
				interfaceFile.create(interfaceContentStream, true, null);

			MSPLPlugin.addProject(project,
					new InterfaceProject(selectProject.getSelectedProject(),
							interfaceFile));
		} catch (CoreException e) {
			e.printStackTrace();
		}

		return true;
	}
}
