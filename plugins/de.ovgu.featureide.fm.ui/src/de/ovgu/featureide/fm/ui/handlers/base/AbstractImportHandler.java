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
package de.ovgu.featureide.fm.ui.handlers.base;

import static de.ovgu.featureide.fm.core.localization.StringTable.FILE;
import static de.ovgu.featureide.fm.core.localization.StringTable.NOT_FOUND;
import static de.ovgu.featureide.fm.core.localization.StringTable.SPECIFIED_FILE_WASNT_FOUND;
import static de.ovgu.featureide.fm.core.localization.StringTable.XML;

import java.io.File;
import java.nio.file.Paths;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Abstract class with core functionality to import FeatureModels.</br> Implementing classes mainly provide a specific FeatureModelReader.
 *
 * @author Fabian Benduhn
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public abstract class AbstractImportHandler extends AFileHandler {

	@Override
	protected final void singleAction(IFile outputFile) {
		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.OPEN);
		fileDialog.setOverwrite(false);
		setFilter(fileDialog);

		File inputFile;
		while (true) {
			final String filepath = fileDialog.open();
			if (filepath == null) {
				return;
			}
			inputFile = new File(filepath);
			if (inputFile.exists()) {
				break;
			}
			MessageDialog.openInformation(new Shell(), FILE + NOT_FOUND, SPECIFIED_FILE_WASNT_FOUND);
		}

		final IFeatureModelFormat modelFormat = setModelReader();
		IFeatureModel fm = null;
		try {
			fm = FMFactoryManager.getFactory(inputFile.getAbsolutePath(), modelFormat).createFeatureModel();
		} catch (final NoSuchExtensionException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		if (fm != null) {
			final ProblemList errors = SimpleFileHandler.load(inputFile.toPath(), fm, modelFormat).getErrors();
			if (!errors.isEmpty()) {
				final StringBuilder sb = new StringBuilder("Error while loading file: \n");
				for (final Problem problem : errors) {
					sb.append("Line ");
					sb.append(problem.getLine());
					sb.append(": ");
					sb.append(problem.getMessage());
					sb.append("\n");
				}
				MessageDialog.openWarning(new Shell(), "Warning!", sb.toString());
			} else {
				SimpleFileHandler.save(Paths.get(outputFile.getLocationURI()), fm, new XmlFeatureModelFormat());
				try {
					openFileInEditor(outputFile);
				} catch (final PartInitException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
		}
	}

	protected void setFilter(FileDialog fileDialog) {
		fileDialog.setFilterExtensions(new String[] { "*.xml" });
		fileDialog.setFilterNames(new String[] { XML });
	}

	/**
	 * Opens the imported model in a new editor. If it is already open, the editor will be closed first.
	 *
	 * @throws PartInitException
	 */
	private void openFileInEditor(IFile outputFile) throws PartInitException {
		final IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		final IEditorInput editorInput = new FileEditorInput(outputFile);
		final IEditorReference[] refs = page.getEditorReferences();
		for (int i = 0; i < refs.length; i++) {
			if (refs[i].getEditorInput().equals(editorInput)) {
				page.closeEditor(refs[i].getEditor(false), false);
				break;
			}

		}
		IDE.openEditor(page, outputFile);
	}

	/**
	 * Returns an instance of {@link IFeatureModelFormat}.
	 */
	protected abstract IFeatureModelFormat setModelReader();
}
