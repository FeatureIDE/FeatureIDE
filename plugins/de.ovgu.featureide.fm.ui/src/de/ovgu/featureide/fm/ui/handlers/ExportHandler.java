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
package de.ovgu.featureide.fm.ui.handlers;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.ui.handlers.base.AFileHandler;

public class ExportHandler extends AFileHandler {

	@Override
	protected void singleAction(IFile modelFile) {
		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		final List<IFeatureModelFormat> formatExtensions = FMFormatManager.getInstance().getExtensions();
		setFilter(fileDialog, formatExtensions);

		final Path modelFilePath = Paths.get(modelFile.getLocationURI());
		fileDialog.setFileName(FileHandler.getFileName(modelFilePath));

		// Ask for file name
		final String filepath = fileDialog.open();
		if (filepath == null) {
			return;
		}

		final FileHandler<IFeatureModel> fileHandler = FeatureModelManager.load(modelFilePath);
		if (!fileHandler.getLastProblems().containsError()) {
			FileHandler.save(Paths.get(filepath), fileHandler.getObject(), formatExtensions.get(fileDialog.getFilterIndex()));
		}
	}

	protected void setFilter(final FileDialog fileDialog, final List<IFeatureModelFormat> formatExtensions) {
		int countWritableFormats = 0;
		for (final IFeatureModelFormat format : formatExtensions) {
			if (format.supportsWrite()) {
				countWritableFormats++;
			}
		}
		final String[] names = new String[countWritableFormats];
		final String[] extensions = new String[countWritableFormats];
		int index = 0;
		int defaultFilterIndex = -1;
		for (final IFeatureModelFormat format : formatExtensions) {
			if (format.supportsWrite()) {
				if (XmlFeatureModelFormat.ID.equals(format.getId())) {
					defaultFilterIndex = index;
				}
				final String extension = "*." + format.getSuffix();
				names[index] = format.getName() + " " + extension;
				extensions[index++] = extension;
			}
		}

		fileDialog.setFilterNames(names);
		fileDialog.setFilterExtensions(extensions);
		if (defaultFilterIndex > -1) {
			fileDialog.setFilterIndex(defaultFilterIndex);
		}
		fileDialog.setOverwrite(true);
	}

}
