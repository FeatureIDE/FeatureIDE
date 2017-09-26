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

import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

public abstract class AbstractExportHandler extends AFileHandler {

	@Override
	protected final void singleAction(IFile modelFile) {
		// Ask for file name
		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		configureFileDialog(fileDialog);
		final String filepath = fileDialog.open();
		if (filepath == null) {
			return;
		}

		final Path path = Paths.get(modelFile.getLocationURI());
		final IFeatureModelFormat format = FMFormatManager.getInstance().getFormatByFileName(modelFile.getName());
		IFeatureModelFactory factory;
		try {
			factory = FMFactoryManager.getFactory(path.toString(), format);
		} catch (final NoSuchExtensionException e) {
			Logger.logError(e);
			factory = FMFactoryManager.getDefaultFactory();
		}
		final IFeatureModel fm = factory.createFeatureModel();

		final FileHandler<IFeatureModel> handler = new FileHandler<>(fm);
		// Read model
		handler.read(path, format);
		handler.write(Paths.get(filepath), getFormat());
	}

	/**
	 * Returns an instance of {@link IFeatureModelFormat}.
	 */
	protected abstract IFeatureModelFormat getFormat();

	protected void configureFileDialog(FileDialog fileDialog) {
		fileDialog.setOverwrite(true);
	}

}
