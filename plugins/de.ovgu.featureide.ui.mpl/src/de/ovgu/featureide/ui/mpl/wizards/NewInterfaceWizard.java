/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.mpl.wizards;

import de.ovgu.featureide.fm.ui.wizards.AbstractWizard;
import de.ovgu.featureide.ui.mpl.MPLUIPlugin;
import de.ovgu.featureide.ui.mpl.wizards.page.SelectFeaturesWizardPage;
import de.ovgu.featureide.ui.mpl.wizards.page.SelectProjectWizardPage;

public class NewInterfaceWizard extends AbstractWizard {
	public static final String ID = MPLUIPlugin.PLUGIN_ID + ".wizards.InterfaceWizard";
	
	public NewInterfaceWizard(String title) {
		super(title);
	}

	@Override
	public void addPages() {
		addPage(new SelectProjectWizardPage());
		addPage(new SelectFeaturesWizardPage());
	}

	protected SelectProjectWizardPage selectProject;
	protected SelectFeaturesWizardPage selectFeatures;

	@Override
	public boolean performFinish() {
//		FeatureModel fm = selectFeatures.createFeatureModel();
//
//		String projectName = fm.getRoot().getName();
//		String interfaceName = "I" + projectName;
//
//		fm.getRoot().setName(interfaceName);
//
//		VelvetFeatureModelWriter modelWriter = new VelvetFeatureModelWriter(fm,
//				true);
//		String interfaceContent = modelWriter.writeToString();
//
//		String importContent = String.format(
//				"concept %s : %s impl %s", projectName, projectName,
//				interfaceName);

//		try {
//			// create interface
//			
//			IFolder mplFolder = project.getFolder("Interfaces");
//			if (!mplFolder.exists())
//				mplFolder.create(true, true, null);
//
//			IFile interfaceFile = mplFolder.getFile(interfaceName + ".velvet");
//
//			// TODO: warning for existing interface file
//			if (!interfaceFile.exists()) {
//				ByteArrayInputStream interfaceContentStream = new ByteArrayInputStream(
//						interfaceContent.getBytes());
//				interfaceFile.create(interfaceContentStream, true, null);
//				interfaceContentStream.close();
//			}
//
//			// create import velvet
//			IFolder importFolder = project.getFolder("MPL");
//			if (!importFolder.exists())
//				importFolder.create(true, true, null);
//
//			IFile importFile = importFolder.getFile(projectName + ".velvet");
//
//			// TODO: warning for existing import file
//			if (!importFile.exists()) {
//				ByteArrayInputStream importContentStream = new ByteArrayInputStream(
//						importContent.getBytes());
//				importFile.create(importContentStream, true, null);
//				importContentStream.close();
//			}
//		} catch (CoreException e) {
//			e.printStackTrace();
//		} catch (IOException e) {
//			e.printStackTrace();
//		}

		return true;
	}
}
