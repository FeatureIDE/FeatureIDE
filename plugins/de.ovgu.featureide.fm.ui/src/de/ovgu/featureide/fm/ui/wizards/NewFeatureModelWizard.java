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

import static de.ovgu.featureide.fm.core.localization.StringTable.FILE_NAME_MUST_BE_SPECIFIED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_FILE_WAS_NOT_ADDED_TO_FILESYSTEM;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_MODEL_FILE_MUST_HAVE_FILE_EXTENSION_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FILE_ALREADY_EXISTS_;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;

/**
 * A Wizard to create a new Feature Model file.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public class NewFeatureModelWizard extends AbstractNewFileWizard<IFeatureModelFormat> implements INewWizard {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".wizard.NewFeatureModelWizard";

	public NewFeatureModelWizard() {
		setWindowTitle(NEW_FEATURE_MODEL);
	}

	@Override
	public boolean performFinish() {
		final IFeatureModelFormat format = ((NewFeatureModelFileFormatPage) formatPage).getFormat();
		final Path fmPath = getNewFilePath(format);
		IFeatureModel featureModel;
		try {
			featureModel = FMFactoryManager.getFactory(fmPath.toString(), format).createFeatureModel();
		} catch (NoSuchExtensionException e) {
			Logger.logError(e);
			featureModel = FMFactoryManager.getEmptyFeatureModel();
		}
		featureModel.createDefaultValues("");
		FileHandler.save(fmPath, featureModel, format);
		String fileName = locationPage.getFileName();
		IFile modelFile = ResourcesPlugin.getWorkspace().getRoot().getFile(locationPage.getContainerFullPath().append(fileName + "." + format.getSuffix()));

		assert (Files.exists(fmPath)) : NEW_FILE_WAS_NOT_ADDED_TO_FILESYSTEM;
		try {
			// open editor
			FMUIPlugin.getDefault().openEditor(FeatureModelEditor.ID, modelFile);
		} catch (final Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return true;
	}

	@Override
	public Path getNewFilePath(IFeatureModelFormat format) {
		String fileName = locationPage.getFileName();
		if (!fileName.matches(".+\\." + Pattern.quote(format.getSuffix()))) {
			fileName += "." + format.getSuffix();
		}
		return getFullPath(fileName);
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		formatPage = new NewFeatureModelFileFormatPage();
		locationPage = new NewFeatureModelFileLocationPage("location", selection);
	}
	

}
