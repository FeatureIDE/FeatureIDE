/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

public abstract class AbstractExportHandler<T> extends AFileHandler {

	@Override
	protected final void singleAction(IFile inputFile) {
		// Ask for file name
		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		configureFileDialog(fileDialog);
		final String outputFile = fileDialog.open();
		if (outputFile == null) {
			return;
		}

		final Path path = Paths.get(inputFile.getLocationURI());
		final IPersistentFormat<T> format = getInputFormat(path);

		final FileHandler<T> handler = new FileHandler<>(getObject(path, format));
		if (handler.read(path, format)) {
			handler.write(Paths.get(outputFile), getOutputFormat());
		}
	}

	protected abstract T getObject(Path path, IPersistentFormat<T> format);

	/**
	 * Returns an instance of {@link IPersistentFormat}.
	 */
	protected abstract IPersistentFormat<T> getOutputFormat();

	protected abstract IPersistentFormat<T> getInputFormat(Path path);

	protected void configureFileDialog(FileDialog fileDialog) {
		fileDialog.setOverwrite(true);
	}

}
