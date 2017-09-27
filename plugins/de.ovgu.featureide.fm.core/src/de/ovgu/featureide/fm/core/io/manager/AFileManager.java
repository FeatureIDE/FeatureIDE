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
import java.nio.charset.Charset;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.event.DefaultEventManager;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.event.IEventManager;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
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
public abstract class AFileManager<T> implements IFileManager<T>, IEventManager {

	public static abstract class ObjectCreator<T> {

		private final Class<T> objectClass;
		private final Class<? extends IFileManager<T>> fileManagerClass;
		private final FormatManager<? extends IPersistentFormat<T>> formatManager;

		public ObjectCreator(Class<T> objectClass, Class<? extends IFileManager<T>> fileManagerClass,
				FormatManager<? extends IPersistentFormat<T>> formatManager) {
			this.objectClass = objectClass;
			this.fileManagerClass = fileManagerClass;
			this.formatManager = formatManager;
		}

		protected abstract T createObject(Path path, final IPersistentFormat<T> format) throws NoSuchExtensionException;
	}

	public static final Charset DEFAULT_CHARSET = Charset.forName("UTF-8");

	private static final Map<String, IFileManager<?>> map = new HashMap<>();

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
	public static <R extends IFileManager<?>> R getInstance(Path path) {
		return (R) map.get(constructAbsolutePath(path));
	}

	/**
	 * Checks whether there is already an instance.
	 *
	 * @param path The path pointing to the file.
	 * @return {@code true} if there is an instance, {@code false} otherwise
	 */
	public static final boolean hasInstance(Path path) {
		return map.containsKey(constructAbsolutePath(path));
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
		return (R) map.remove(constructAbsolutePath(path));
	}

	private static final String constructAbsolutePath(Path path) {
		final Path p = path.toAbsolutePath();
		final String absolutePath = p.toString();
		return absolutePath;
	}

	public static final <T> FileHandler<T> getFileHandler(Path path, ObjectCreator<T> objectCreator) {
		final FileHandler<T> fileHandler = new FileHandler<>(path, null, null);
		final String content = fileHandler.getContent();

		if (content != null) {
			final String fileName = path.getFileName().toString();
			final IPersistentFormat<T> format = objectCreator.formatManager.getFormatByContent(content, fileName);
			if (format == null) {
				fileHandler.getLastProblems().add(new Problem(new FormatManager.NoSuchExtensionException("No format found for file \"" + fileName + "\"!")));
			} else {
				try {
					final T featureModel = objectCreator.createObject(path, format);
					fileHandler.setObject(featureModel);
					fileHandler.setFormat(format);
					fileHandler.parse(content);
				} catch (final NoSuchExtensionException e) {
					fileHandler.getLastProblems().add(new Problem(e));
				}
			}
		}

		return fileHandler;
	}

	@SuppressWarnings("unchecked")
	@CheckForNull
	public static final <T, R extends IFileManager<T>> R newInstance(Path path, ObjectCreator<T> objectCreator) {
		final String absolutePath = constructAbsolutePath(path);
		final SimpleFileHandler<T> fileHandler = getFileHandler(path, objectCreator);

		try {
			final Constructor<? extends IFileManager<T>> constructor =
				objectCreator.fileManagerClass.getDeclaredConstructor(objectCreator.objectClass, String.class, IPersistentFormat.class);
			constructor.setAccessible(true);
			final IFileManager<?> instance = constructor.newInstance(fileHandler.getObject(), absolutePath, fileHandler.getFormat());
			map.put(absolutePath, instance);
			instance.getLastProblems().addAll(fileHandler.getLastProblems());
			return (R) objectCreator.fileManagerClass.cast(instance);
		} catch (ReflectiveOperationException | SecurityException | IllegalArgumentException e) {
			Logger.logError(e);
			return null;
		}
	}

	@SuppressWarnings("unchecked")
	@CheckForNull
	public static final <T, R extends IFileManager<T>> R getInstance(Path path, ObjectCreator<T> objectCreator) {
		final IFileManager<?> instance = getInstance(path);
		if (instance == null) {
			return newInstance(path, objectCreator);
		} else if (objectCreator.fileManagerClass.isInstance(instance)) {
			return (R) objectCreator.fileManagerClass.cast(instance);
		} else {
			return null;
		}
	}

	private final IEventManager eventManager = new DefaultEventManager();
	private final ProblemList lastProblems = new ProblemList();

	protected final Object syncObject = new Object();

	protected final IPersistentFormat<T> format;

	protected final String absolutePath;
	protected final Path path;

	protected T persistentObject;
	protected T variableObject;
	protected T emptyObject;

	private boolean modifying = false;

	protected AFileManager(T object, String absolutePath, IPersistentFormat<T> format) {
		this.format = format;
		this.absolutePath = absolutePath;
		path = Paths.get(absolutePath);

		variableObject = object;
		emptyObject = copyObject(object);

		if (FileSystem.exists(path)) {
			try {
				final String content = new String(FileSystem.read(path), DEFAULT_CHARSET);
				final ProblemList problems = format.getInstance().read(variableObject, content);
				if (problems != null) {
					lastProblems.addAll(problems);
				}
			} catch (final Exception e) {
				handleException(e);
			}
		}
		persistentObject = copyObject(variableObject);
	}

	@Override
	public void addListener(IEventListener listener) {
		eventManager.addListener(listener);
	}

	protected abstract T copyObject(T oldObject);

	@Override
	public T getObject() {
		return persistentObject;
	}

	@Override
	public T editObject() {
		return variableObject;
	}

	public void setModifying(boolean modifying) {
		synchronized (syncObject) {
			this.modifying = modifying;
		}
	}

	@Override
	public void fireEvent(FeatureIDEEvent event) {
		eventManager.fireEvent(event);
	}

	@Override
	public IPersistentFormat<T> getFormat() {
		return format;
	}

	@Override
	public ProblemList getLastProblems() {
		return lastProblems;
	}

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
	}

	@Override
	public boolean read() {
		if (!FileSystem.exists(path)) {
			return false;
		}
		final boolean success, changed;
		synchronized (syncObject) {
			if (modifying) {
				return true;
			}
			lastProblems.clear();
			final T tempObject = copyObject(emptyObject);
			try {
				final String content = new String(FileSystem.read(path), DEFAULT_CHARSET);
				final List<Problem> problemList = format.getInstance().read(tempObject, content);
				if (problemList != null) {
					lastProblems.addAll(problemList);
				}
				changed = !compareObjects(tempObject, persistentObject);
			} catch (final Exception e) {
				handleException(e);
				return false;
			}
			if (changed) {
				persistentObject = tempObject;
			}
			success = lastProblems.isEmpty();
		}
		if (changed) {
			ExternalChangeListener.update(this);
		}
		return success;
	}

	// TODO Quickfix for #501. Should be implemented by overriding the current instance pointer.
	@Override
	public void override() {
		synchronized (syncObject) {
			if (modifying) {
				return;
			}
			final String write = format.getInstance().write(persistentObject);
			format.getInstance().read(variableObject, write);
			// variableObject = copyObject(localObject);
			// persistentObject = copyObject(localObject);
		}
		fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_OVERRIDDEN));
	}

	@Override
	public void removeListener(IEventListener listener) {
		eventManager.removeListener(listener);
	}

	/**
	 * Compares two object for equality.<br/> Subclasses should override (implement) this method.
	 *
	 * @param o1 First object.
	 * @param o2 Second object.
	 * @return {@code true} if objects are considered equal, {@code false} otherwise.
	 */
	protected boolean compareObjects(T o1, T o2) {
		final String s1 = format.getInstance().write(o1);
		final String s2 = format.getInstance().write(o2);
		return s1.equals(s2);
	}

	@Override
	public boolean save() {
		final boolean success;
		synchronized (syncObject) {
			lastProblems.clear();
			try {
				if (modifying) {
					return true;
				}
				modifying = true;
				final T tempObject = copyObject(variableObject);
				final byte[] content = format.getInstance().write(tempObject).getBytes(DEFAULT_CHARSET);
				FileSystem.write(path, content);
				persistentObject = copyObject(tempObject);
			} catch (final Exception e) {
				handleException(e);
				return false;
			} finally {
				modifying = false;
			}
			success = lastProblems.isEmpty();
		}
		fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_SAVED));
		return success;
	}

	@Override
	public boolean externalSave(Runnable externalSaveMethod) {
		final boolean success;
		synchronized (syncObject) {
			lastProblems.clear();
			try {
				if (modifying) {
					return true;
				}
				modifying = true;
				final T tempObject = copyObject(variableObject);
				externalSaveMethod.run();
				persistentObject = copyObject(tempObject);
			} catch (final Exception e) {
				handleException(e);
				return false;
			} finally {
				modifying = false;
			}
			success = lastProblems.isEmpty();
		}
		fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_SAVED));
		return success;
	}

	@Override
	public void dispose() {
		removeInstance(Paths.get(absolutePath));
		synchronized (syncObject) {
			persistentObject = null;
			variableObject = null;
		}
	}

	@Override
	public String getAbsolutePath() {
		return absolutePath;
	}

	@Override
	public Path getPath() {
		return path;
	}

	@Override
	public String toString() {
		return "File manager for " + absolutePath;
	}

}
