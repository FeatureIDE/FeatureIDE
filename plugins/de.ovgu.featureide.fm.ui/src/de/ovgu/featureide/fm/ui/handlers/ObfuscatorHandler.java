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

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.editing.FeatureModelObfuscator;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.ui.handlers.base.AFileHandler;

public class ObfuscatorHandler extends AFileHandler {

	@Override
	protected final void singleAction(IFile modelFile) {
		// Ask for file name

		final List<IFeatureModelFormat> formatExtensions = FMFormatManager.getInstance().getExtensions();
		final String[] names = new String[formatExtensions.size()];
		final String[] extensions = new String[formatExtensions.size()];
		int index = 0;
		for (final IFeatureModelFormat format : formatExtensions) {
			final String extension = "*." + format.getSuffix();
			names[index] = format.getName() + " " + extension;
			extensions[index++] = extension;
		}

		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		fileDialog.setFilterNames(names);
		fileDialog.setFilterExtensions(extensions);
		fileDialog.setFileName("obfuscated_model");
		fileDialog.setOverwrite(true);

		final String filepath = fileDialog.open();
		if (filepath == null) {
			return;
		}

		final Path modelFilePath = Paths.get(modelFile.getLocationURI());
		final FileHandler<IFeatureModel> fileHandler = FeatureModelManager.load(modelFilePath);
		if (!fileHandler.getLastProblems().containsError()) {
			final IFeatureModel ofm = LongRunningWrapper.runMethod(new FeatureModelObfuscator(fileHandler.getObject(), getSalt(modelFilePath)));
			FileHandler.save(Paths.get(filepath), ofm, formatExtensions.get(fileDialog.getFilterIndex()));
		}
	}

	private String getSalt(Path modelFilePath) {
		final Path saltPath = modelFilePath.getParent().resolve(modelFilePath.getFileName().toString() + ".salt");
		if (Files.exists(saltPath)) {
			try {
				return new String(Files.readAllBytes(saltPath), StandardCharsets.UTF_8);
			} catch (final IOException e) {
				Logger.logWarning("Salt file could not be read! -> Creating new random salt.");
			}
		}
		return getRandomSalt(saltPath);
	}

	private String getRandomSalt(final Path saltPath) {
		try {
			final String randomSalt = FeatureModelObfuscator.getRandomSalt();
			Files.write(saltPath, randomSalt.getBytes(), StandardOpenOption.CREATE_NEW, StandardOpenOption.WRITE);
			return randomSalt;
		} catch (final Exception e) {
			Logger.logWarning("Salt file could not be created!");
			return null;
		}
	}

}
