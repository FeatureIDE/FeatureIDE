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

import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_FILE_WAS_NOT_ADDED_TO_FILESYSTEM;

import java.nio.file.Paths;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

/**
 * A Wizard to create a new Feature Model file.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
// TOOD add copy of an other model file
public class NewFeatureModelWizard extends Wizard implements INewWizard {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".wizard.NewFeatureModelWizard";

	private NewFeatureModelWizardPage page;
	private IProject project = null;

	@Override
	public boolean performFinish() {
		final IPath fullFilePath = new Path(page.fileName.getText());

		if ((project == null) || !createRelativeFile(fullFilePath, project)) {
			boolean foundParent = false;
			for (final IProject otherProject : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
				if (createRelativeFile(fullFilePath, otherProject)) {
					foundParent = true;
					break;
				}
			}
			if (!foundParent) {
				final XmlFeatureModelFormat format = new XmlFeatureModelFormat();
				IFeatureModel featureModel;
				final String filePathString = fullFilePath.toOSString();
				try {
					featureModel = FMFactoryManager.getFactory(filePathString, format).createFeatureModel();
				} catch (final NoSuchExtensionException e) {
					Logger.logError(e);
					featureModel = FMFactoryManager.getEmptyFeatureModel();
				}
				featureModel.createDefaultValues("");
				SimpleFileHandler.save(Paths.get(filePathString), featureModel, format);
			}
		}
		assert (fullFilePath.toFile().exists()) : NEW_FILE_WAS_NOT_ADDED_TO_FILESYSTEM;
		return true;
	}

	private void open(IFile file) {
		final IWorkbenchWindow dw = FMUIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow();
		final IWorkbenchPage page = dw.getActivePage();
		if (page != null) {
			IContentType contentType = null;
			try {
				final IContentDescription description = file.getContentDescription();
				if (description != null) {
					contentType = description.getContentType();
				}
				IEditorDescriptor desc = null;
				if (contentType != null) {
					desc = PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName(), contentType);
				} else {
					desc = PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName());
				}
				if (desc != null) {
					page.openEditor(new FileEditorInput(file), desc.getId());
				}
			} catch (final CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	private boolean createRelativeFile(IPath fullFilePath, IProject parentProject) {
		if (parentProject.getLocation().isPrefixOf(fullFilePath)) {
			final IFile file = parentProject.getFile(fullFilePath.makeRelativeTo(parentProject.getLocation()));

			final java.nio.file.Path path = Paths.get(file.getLocationURI());

			final IFeatureModelFormat format = FMFormatManager.getInstance().getFormatByFileName(path.getFileName().toString());
			IFeatureModelFactory factory;
			try {
				factory = FMFactoryManager.getFactory(path.toString(), format);
			} catch (final NoSuchExtensionException e) {
				Logger.logError(e);
				factory = FMFactoryManager.getDefaultFactory();
			}
			final IFeatureModel featureModel = factory.createFeatureModel();
			featureModel.createDefaultValues("");
			FMComposerManager.getFMComposerExtension(file.getProject());

			FeatureModelManager.save(featureModel, path);

			open(file);
			return true;
		}
		return false;
	}

	@Override
	public void addPages() {
		setWindowTitle(NEW_FEATURE_MODEL);
		addPage(page);
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		final IResource res = SelectionWrapper.init(selection, IResource.class).getNext();
		if (res != null) {
			project = res.getProject();
			page = new NewFeatureModelWizardPage("", project);
		} else {
			page = new NewFeatureModelWizardPage("", null);
		}
	}
}
