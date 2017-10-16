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
package de.ovgu.featureide.fm.core.io.manager;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.base.event.IEventManager;

/**
 * Responsible to load and save all information from / to a file.<br/> To get an instance use the {@link FileManagerMap}.
 *
 * @author Sebastian Krieter
 */
public abstract class FileManagerMap<T> implements IFileManager<T>, IEventManager {

	private static final Map<String, IFileManager<?>> map = new HashMap<>();

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
	public static <R extends IFileManager<?>> R getInstance(Path path) throws ClassCastException {
		final String absolutePath = constructAbsolutePath(path);
		synchronized (map) {
			return (R) map.get(absolutePath);
		}
	}

	/**
	 * Checks whether there is already an instance.
	 *
	 * @param path The path pointing to the file.
	 * @return {@code true} if there is an instance, {@code false} otherwise
	 */
	public static final boolean hasInstance(Path path) {
		final String absolutePath = constructAbsolutePath(path);
		synchronized (map) {
			return map.containsKey(absolutePath);
		}
	}

	/**
	 * Removes and returns an instance of a {@link IFileManager} for a certain file.
	 *
	 * @param path The path pointing to the file.
	 *
	 * @return The manager instance for the specified file, or {@code null} if no instance was created yet.
	 *
	 * @throws ClassCastException When the found instance is no subclass of R.
	 */
	@SuppressWarnings("unchecked")
	@CheckForNull
	public static final <R extends IFileManager<?>> R removeInstance(Path path) {
		final String absolutePath = constructAbsolutePath(path);
		synchronized (map) {
			final IFileManager<?> fileManager = map.remove(absolutePath);
			if (fileManager != null) {
				fileManager.dispose();
			}
			return (R) fileManager;
		}
	}

	public static final String constructAbsolutePath(Path path) {
		return path.toAbsolutePath().toString();
	}

	/**
	 * Adds a new {@link IFileManager file manager} instance to the map, unless the file of the given file manager is already associated with another file
	 * manager.
	 *
	 * @param instance the file manager
	 */
	public static void addInstance(IFileManager<?> instance) {
		final String absolutePath = instance.getAbsolutePath();
		synchronized (map) {
			if (!map.containsKey(absolutePath)) {
				map.put(absolutePath, instance);
			}
		}
	}

}
