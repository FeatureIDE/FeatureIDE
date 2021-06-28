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
package de.ovgu.featureide.fm.ui.handlers;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.FeatureModelObfuscator;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * {@link ObfuscatorHandler} receives a {@link IFeatureModel}, calls the correct {@link IFeatureModelFactory} depending on the feature model format to have it
 * obfuscated, and saves it in a new feature model file.
 *
 * @author Sebastian Krieter
 * @author Rahel Arens
 * @author Benedikt Jutz
 */
public class ObfuscatorHandler extends FMExportHandler {

	private static final String SALT_FILENAME_PATTERN = ".%s.salt";

	@Override
	protected String getDefaultFileName(Path modelFilePath) {
		return "obfuscated_" + FileHandler.getFileName(modelFilePath);
	}

	@Override
	protected void save(IPersistentFormat<IFeatureModel> format, FileHandler<IFeatureModel> fileHandler, Path path) {
		if (!fileHandler.getLastProblems().containsError()) {
			IFeatureModel ofm = null;
			try {
				ofm = FMFactoryManager.getInstance().getFactory(format).createObfuscatedFeatureModel((IFeatureModel) fileHandler.getObject(),
						getSalt(fileHandler.getPath()));
			} catch (final NoSuchExtensionException e) {
				e.printStackTrace();
			}
			FileHandler.save(path, ofm, format);
		}
	}

	/**
	 * Reads and returns the salt from the salt file with ending ".salt" that has been assigned to the feature model in the file at modelFilePath. If no such
	 * file exists, return a new salt string instead, and save it.
	 *
	 * @param modelFilePath - {@link Path}
	 * @return - {@link String}
	 */
	public String getSalt(Path modelFilePath) {
		final Path saltPath = modelFilePath.getParent().resolve(String.format(SALT_FILENAME_PATTERN, modelFilePath.getFileName().toString()));
		if (Files.exists(saltPath)) {
			try {
				return new String(Files.readAllBytes(saltPath), StandardCharsets.UTF_8);
			} catch (final IOException e) {
				Logger.logWarning("Salt file could not be read! -> Creating new random salt.");
			}
		}
		return getRandomSalt(saltPath);
	}

	/**
	 * Creates a new salt and saves it in the file with the path saltPath.
	 *
	 * @param saltPath - {@link Path}
	 * @return {@link String}
	 */
	private String getRandomSalt(final Path saltPath) {
		final String randomSalt = FeatureModelObfuscator.getRandomSalt();
		try {
			Files.write(saltPath, randomSalt.getBytes(StandardCharsets.UTF_8), StandardOpenOption.CREATE_NEW, StandardOpenOption.WRITE);
		} catch (final Exception e) {
			Logger.logWarning("Salt file could not be created!");
		}
		return randomSalt;
	}

}
