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
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.IFeatureModelWriter;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

public abstract class AbstractExportHandler extends AFileHandler {

	@Override
	protected final void singleAction(IFile modelFile) {
		try {
			final FeatureModel fm = new FeatureModel();

			// Read model
			final FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(fm));
			reader.readFromFile(modelFile);

			// Get writer
			final IFeatureModelWriter fmWriter = getFeatureModelWriter(fm);
			if (fmWriter == null) {
				return;
			}

			// Ask for file name
			FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
			configureFileDialog(fileDialog);
			final String filepath = fileDialog.open();
			if (filepath == null) {
				return;
			}

			// Write model
			fmWriter.writeToFile(new File(filepath));

			modelFile.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (FileNotFoundException | UnsupportedModelException | CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param fm
	 * @return
	 */
	protected abstract IFeatureModelWriter getFeatureModelWriter(FeatureModel fm);

	protected void configureFileDialog(FileDialog fileDialog) {
		fileDialog.setOverwrite(true);
	}

}
