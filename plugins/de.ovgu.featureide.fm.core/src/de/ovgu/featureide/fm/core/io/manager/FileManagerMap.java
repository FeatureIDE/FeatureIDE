/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
import java.lang.reflect.Constructor;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Maps paths to {@link IFileManager file managers}.
 * 
 * @author Sebastian Krieter
 */
public abstract class FileManagerMap {

	private static final Map<String, IFileManager<?>> map = new HashMap<>();

	public static String constructExtraPath(String path, IPersistentFormat<?> format) throws IllegalArgumentException {
		final Path mainPath = Paths.get(path).toAbsolutePath();
		final Path mainFileNamePath = mainPath.getFileName();
		if (mainFileNamePath != null) {
			final String mainFileNameString = mainFileNamePath.toString();
			final Path subpath = mainPath.subpath(0, mainPath.getNameCount() - 1);
			final Path root = mainPath.getRoot();
			if (subpath != null && root != null) {
				final Path extraFolder = root.resolve(subpath.resolve(".featureide").resolve(mainFileNameString));

				if (!FileSystem.exists(extraFolder)) {
					try {
						FileSystem.mkDir(extraFolder);
					} catch (IOException e) {
						Logger.logError(e);
					}
				}

				return extraFolder.resolve(mainFileNameString + "." + format.getSuffix()).toString();
			}
		}
		throw new IllegalArgumentException("Path " + path + " can not be transformed.");
	}

	protected static final String constructAbsolutePath(String path) {
		final Path p = Paths.get(path).toAbsolutePath();
		final String absolutePath = p.toString();
		return absolutePath;
	}

	/**
	 * Returns the instance of a {@link IFileManager} for a certain file.
	 * 
	 * @param path The path pointing to the file.
	 * 
	 * @return The manager instance for the specified file, or {@code null} if no instance was created yet.
	 */
	@CheckForNull
	public static IFileManager<?> getFileManager(String path) {
		return map.get(constructAbsolutePath(path));
	}

	/**
	 * Checks whether there is already an instance.
	 * 
	 * @param path
	 * @return
	 */
	public static boolean hasInstance(String path) {
		return map.containsKey(constructAbsolutePath(path));
	}

	/**
	 * Returns and casts an instance of a {@link IFileManager} for a certain file.
	 * 
	 * @param path The path pointing to the file.
	 * 
	 * @return The manager instance for the specified file, or {@code null} if no instance was created yet.
	 * 
	 * @throws ClassCastException When the found instance is no subclass of R.
	 */
	@SuppressWarnings("unchecked")
	@CheckForNull
	public static <T, R extends IFileManager<T>> R getInstance(String path) {
		return (R) map.get(constructAbsolutePath(path));
	}

	public static <T, R extends AFileManager<T>> R getInstance(T object, String path, IPersistentFormat<T> format, Class<R> c, Class<T> t) {
		final String absolutePath = constructAbsolutePath(path);
		final IFileManager<?> manager = map.get(absolutePath);
		if (manager != null) {
			return c.cast(manager);
		} else {
			try {
				final Constructor<R> constructor = c.getDeclaredConstructor(t, String.class, IPersistentFormat.class);
				constructor.setAccessible(true);
				final R newInstance = constructor.newInstance(object, absolutePath, format);
				map.put(absolutePath, newInstance);
				return newInstance;
			} catch (ReflectiveOperationException | SecurityException | IllegalArgumentException e) {
				Logger.logError(e);
				return null;
			}
		}
	}

	public static IFileManager<?> remove(String path) {
		return map.remove(constructAbsolutePath(path));
	}

}
