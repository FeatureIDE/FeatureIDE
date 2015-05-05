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
package de.ovgu.featureide.fm.ui.handlers.base;

import java.io.File;
import java.io.FileNotFoundException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
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

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Abstract class with core functionality to import FeatureModels.</br>
 * Implementing classes mainly provide a specific FeatureModelReader.
 * 
 * @author Fabian Benduhn
 * @author Sebastian Krieter
 */
public abstract class AbstractImportHandler extends AFileHandler {
	private IFeatureModelReader modelReader;

	@Override
	protected final void singleAction(IFile outputFile) {
		try {
			if (MessageDialog.openQuestion(new Shell(), "Warning!", "This will override the current model irrepealable! Proceed?")) {
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
					MessageDialog.openInformation(new Shell(), "File " + "not Found", "Specified file wasn't found");
				}

				final FeatureModel fm = createFeatureModel();
				modelReader = setModelReader(fm);
				modelReader.readFromFile(inputFile);

				final FeatureModelWriterIFileWrapper fmWriter = new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(fm));
				fmWriter.writeToFile(outputFile);
				outputFile.refreshLocal(IResource.DEPTH_ZERO, null);
				openFileInEditor(outputFile);
			}
		} catch (FileNotFoundException | CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		} catch (UnsupportedModelException e) {
			MessageDialog.openWarning(new Shell(), "Warning!", "Error while loading file: \n " + e.getMessage());
			FMUIPlugin.getDefault().logError(e);
		}
	}

	protected void setFilter(FileDialog fileDialog) {
		fileDialog.setFilterExtensions(new String[] { "*.xml" });
		fileDialog.setFilterNames(new String[] { "XML" });
	}

	protected FeatureModel createFeatureModel() {
		return new FeatureModel();
	}

	/**
	 * Opens the imported model in a new editor. If it is already open, the
	 * editor will be closed first.
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
	 * Returns an instance of IFeatureModelReader.
	 * 
	 * @param fm
	 *            the feature model to initialize the IFeatureModelReader
	 */
	protected abstract IFeatureModelReader setModelReader(FeatureModel fm);
}
