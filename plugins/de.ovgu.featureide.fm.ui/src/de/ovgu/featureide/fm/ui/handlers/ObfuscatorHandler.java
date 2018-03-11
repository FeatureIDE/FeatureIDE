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
import java.nio.file.StandardOpenOption;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.FeatureModelObfuscator;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

public class ObfuscatorHandler extends FMExportHandler {

	private static final String SALT_FILENAME_PATTERN = ".%s.salt";

	@Override
	protected String getDefaultFileName(Path modelFilePath) {
		return "obfuscated_" + FileHandler.getFileName(modelFilePath);
	}

	@Override
	protected void save(IPersistentFormat<IFeatureModel> format, FileHandler<IFeatureModel> fileHandler, Path path) {
		if (!fileHandler.getLastProblems().containsError()) {
			final IFeatureModel ofm = LongRunningWrapper.runMethod(new FeatureModelObfuscator(fileHandler.getObject(), getSalt(fileHandler.getPath())));
			FileHandler.save(path, ofm, format);
		}
	}

	private String getSalt(Path modelFilePath) {
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

	private String getRandomSalt(final Path saltPath) {
		try {
			final String randomSalt = FeatureModelObfuscator.getRandomSalt();
			Files.write(saltPath, randomSalt.getBytes(StandardCharsets.UTF_8), StandardOpenOption.CREATE_NEW, StandardOpenOption.WRITE);
			return randomSalt;
		} catch (final Exception e) {
			Logger.logWarning("Salt file could not be created!");
			return null;
		}
	}

}
