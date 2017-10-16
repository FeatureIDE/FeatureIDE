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

import java.io.IOException;
import java.lang.reflect.Constructor;
import java.nio.file.Path;
import java.util.List;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.functional.Functional.ICriticalConsumer;
import de.ovgu.featureide.fm.core.io.ExternalChangeListener;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Responsible to load and save all information from / to a file.<br/> To get an instance use the {@link FileManagerMap}.
 *
 * @author Sebastian Krieter
 */
public class FileManager<T> extends AFileManager<T> {

	/**
	 * Constructs a path for a given file to store additional information.
	 *
	 * @param path The path pointing to the file.
	 * @param format The format for the extra information file.
	 * @return The path to the extra information file.
	 *
	 * @throws IllegalArgumentException If path is empty.
	 */
	public static final Path constructExtraPath(Path path, IPersistentFormat<?> format) throws IllegalArgumentException {
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

	@SuppressWarnings("unchecked")
	@CheckForNull
	private static final <T, R extends IFileManager<T>> R newInstance(Path path, ObjectCreator<T> objectCreator,
			Class<? extends IFileManager<T>> fileManagerClass, FormatManager<? extends IPersistentFormat<T>> formatManager) {
		final SimpleFileHandler<T> fileHandler = SimpleFileHandler.getFileHandler(path, objectCreator, formatManager);

		try {
			final Constructor<? extends IFileManager<T>> constructor = fileManagerClass.getDeclaredConstructor(SimpleFileHandler.class, ObjectCreator.class);
			constructor.setAccessible(true);
			final IFileManager<?> instance = constructor.newInstance(fileHandler, objectCreator);
			FileManagerMap.addInstance(instance);
			instance.getLastProblems().addAll(fileHandler.getLastProblems());
			return (R) fileManagerClass.cast(instance);
		} catch (ReflectiveOperationException | SecurityException | IllegalArgumentException e) {
			Logger.logError(e);
			return null;
		}
	}

	@SuppressWarnings("unchecked")
	@CheckForNull
	protected static final <T, R extends IFileManager<T>> R getInstance(Path path, ObjectCreator<T> objectCreator,
			Class<? extends IFileManager<T>> fileManagerClass, FormatManager<? extends IPersistentFormat<T>> formatManager) {
		final IFileManager<?> instance = FileManagerMap.getInstance(path);
		if (instance == null) {
			return newInstance(path, objectCreator, fileManagerClass, formatManager);
		} else if (fileManagerClass.isInstance(instance)) {
			return (R) fileManagerClass.cast(instance);
		} else {
			return null;
		}
	}

	protected final Path path;

	private final ProblemList lastProblems = new ProblemList();

	protected T lastReadObject = null;

	private boolean modifying = false;

	protected FileManager(SimpleFileHandler<T> fileHandler, ObjectCreator<T> objectCreator) {
		super(fileHandler.getFormat(), FileManagerMap.constructAbsolutePath(fileHandler.getPath()), fileHandler.getObject(), objectCreator);
		this.path = fileHandler.getPath();
	}

	@Override
	public Path getPath() {
		return path;
	}

	@Override
	public ProblemList getLastProblems() {
		return lastProblems;
	}

	@Override
	public boolean read() {
		if (!FileSystem.exists(path)) {
			return false;
		}
		final boolean success, changed;
		synchronized (this) {
			if (modifying) {
				return true;
			}
			lastProblems.clear();
			lastReadObject = objectCreator.createObject();
			try {
				final String content = new String(FileSystem.read(path), SimpleFileHandler.DEFAULT_CHARSET);
				final List<Problem> problemList = format.getInstance().read(lastReadObject, content);
				if (problemList != null) {
					lastProblems.addAll(problemList);
				}
				changed = !objectCreator.compareObjects(lastReadObject, persistentObject.getObject());
			} catch (final Exception e) {
				handleException(e);
				return false;
			}
			success = lastProblems.isEmpty();
			if (changed) {
				persistentObject = objectCreator.createSnapshot(lastReadObject);
			}
		}
		if (changed) {
			ExternalChangeListener.update(this);
		}
		return success;
	}

	// TODO Quickfix for #501. Should be implemented by overriding the current instance pointer.
	@Override
	public void override() {
		synchronized (this) {
			if (modifying) {
				return;
			}
			if (lastReadObject != null) {
				copyPropertiesOnOverride();
				variableObject = lastReadObject;
				lastReadObject = null;
			}
		}
		fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_OVERRIDDEN));
	}

	protected void copyPropertiesOnOverride() {}

	@Override
	public boolean save() {
		return externalSave(new ICriticalConsumer<T>() {

			@Override
			public void invoke(T t) throws IOException {
				FileSystem.write(path, format.getInstance().write(t).getBytes(SimpleFileHandler.DEFAULT_CHARSET));
			}
		});
	}

	@Override
	public boolean externalSave(ICriticalConsumer<T> externalSaveMethod) {
		final boolean success;
		synchronized (this) {
			lastProblems.clear();
			try {
				if (modifying) {
					return true;
				}
				modifying = true;
				final Snapshot<T> tempObject = objectCreator.createSnapshot(variableObject);
				externalSaveMethod.invoke(tempObject.getObject());
				persistentObject = tempObject;
			} catch (final Exception e) {
				handleException(e);
				return false;
			} finally {
				modifying = false;
			}
			success = lastProblems.isEmpty();
		}
		if (success) {
			fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_SAVED));
		}
		return success;
	}

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
	}

	@Override
	public String toString() {
		return "File manager for " + absolutePath;
	}

}
