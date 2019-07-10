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
package de.ovgu.featureide.fm.core.io.manager;

import java.io.IOException;
import java.nio.file.Path;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.impl.FactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;

/**
 * File handling operations for an object of T.
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractIO<T> {

	/**
	 * Constructs a path for a given file to store additional information.
	 *
	 * @param path The path pointing to the file.
	 * @param format The format for the extra information file.
	 * @return The path to the extra information file.
	 *
	 * @throws IllegalArgumentException If path is empty.
	 */
	public final Path constructExtraPath(Path path, IPersistentFormat<T> format) throws IllegalArgumentException {
		final Path mainPath = path.toAbsolutePath();
		final Path mainFileNamePath = mainPath.getFileName();
		if (mainFileNamePath != null) {
			final String mainFileNameString = mainFileNamePath.toString();
			final Path subpath = mainPath.subpath(0, mainPath.getNameCount() - 1);
			final Path root = mainPath.getRoot();
			if ((subpath != null) && (root != null)) {
				final Path extraFolder = root.resolve(subpath.resolve(".featureide").resolve(mainFileNameString));

				if (!FileSystem.exists(extraFolder)) {
					try {
						FileSystem.mkDir(extraFolder);
					} catch (final IOException e) {
						Logger.logError(e);
					}
				}

				return extraFolder.resolve(mainFileNameString + "." + format.getSuffix());
			}
		}
		throw new IllegalArgumentException("Path " + path + " can not be transformed.");
	}

	protected abstract FormatManager<T> getFormatManager();

	protected abstract FactoryManager<T> getFactoryManager();

	public final boolean convert(Path inPath, Path outPath, IPersistentFormat<T> format) {
		final T object = getFileHandler(inPath).getObject();
		if (object == null) {
			return false;
		}
		return convert(inPath, outPath, format);
	}

	@CheckForNull
	public final T load(Path path) {
		final FileHandler<T> fileHandler = getFileHandler(path);
		return (fileHandler == null) ? null : fileHandler.getObject();
	}

	@CheckForNull
	public final T loadFromSource(CharSequence source, Path fileName) {
		final IPersistentFormat<T> format = getFormatManager().getFormatByContent(source, fileName.toString());
		try {
			final T object = getFactoryManager().getFactory(fileName, format).create();
			format.read(object, source);
			return object;
		} catch (final NoSuchExtensionException e) {
			Logger.logError(e);
			return null;
		}
	}

	public final FileHandler<T> getFileHandler(Path path) {
		final FileHandler<T> fileHandler = new FileHandler<>(path, null, null);
		final String content = fileHandler.getContent();

		if (content != null) {
			final String fileName = path.getFileName().toString();
			final IPersistentFormat<T> format = getFormatManager().getFormatByContent(content, fileName);
			if (format == null) {
				fileHandler.getLastProblems().add(new Problem(new FormatManager.NoSuchExtensionException("No format found for file \"" + fileName + "\"!")));
			} else {
				try {
					final T object = getFactoryManager().getFactory(path, format).create();
					fileHandler.setObject(object);
					fileHandler.setFormat(format);
					fileHandler.parse(content);
				} catch (final NoSuchExtensionException e) {
					fileHandler.getLastProblems().add(new Problem(e));
				}
			}
		}

		return fileHandler;
	}

	public final boolean save(T object, Path path, IPersistentFormat<T> format) {
		return !SimpleFileHandler.save(path, object, format).containsError();
	}

}
