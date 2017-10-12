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
package de.ovgu.featureide.fm.ui.wizards;

import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * Holds common behavior of a NewFile Creation Wizard
 * 
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public abstract class AbstractNewFileWizard<T> extends Wizard implements INewWizard {

	protected WizardNewFileCreationPage locationPage;
	protected WizardPage formatPage;

	public abstract Path getNewFilePath(T format);

	protected Path getFullPath(String fileName) {
		return Paths.get(ResourcesPlugin.getWorkspace().getRoot().getFile(locationPage.getContainerFullPath().append(fileName)).getLocationURI());
	}

	protected IFeatureModel defaultFeatureModel() {
		final IFeatureModelFactory factory = FMFactoryManager.getDefaultFactory();
		IFeatureModel newFeatureModel = factory.createFeatureModel();
		final IFeature root = factory.createFeature(newFeatureModel, "root");

		newFeatureModel.addFeature(root);
		newFeatureModel.getStructure().setRoot(root.getStructure());

		return newFeatureModel;
	}

	@Override
	public void addPages() {
		addPage(locationPage);
		addPage(formatPage);
	}
}
