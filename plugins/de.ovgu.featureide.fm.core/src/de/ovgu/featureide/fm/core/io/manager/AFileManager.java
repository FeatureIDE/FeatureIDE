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
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;

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

	public static class FileIdentifier<T> {
		private final Path path;
		private final IPersistentFormat<T> format;

		private FileIdentifier(Path path, IPersistentFormat<T> format) {
			this.path = path.toAbsolutePath().normalize();
			this.format = format;
		}

		@Override
		public int hashCode() {
			int result = format.getId().hashCode();
			result = (31 * result) + path.hashCode();
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if ((obj == null) || (getClass() != obj.getClass())) {
				return false;
			}
			final FileIdentifier<?> other = (FileIdentifier<?>) obj;
			return (format.getId().equals(other.format.getId()) && path.equals(other.path));
		}

		public Path getPath() {
			return path;
		}

		public IPersistentFormat<T> getFormat() {
			return format;
		}

		@Override
		public String toString() {
			return "Path: " + path + ", Format: " + format.getId();
		}

	}

	protected static abstract class ObjectCreator<T> {

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

	private static final Map<FileIdentifier<?>, IFileManager<?>> idMap = new HashMap<>();
	private static final Map<Path, List<IFileManager<?>>> pathMap = new HashMap<>();

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
	 * Checks whether there is already an instance.
	 *
	 * @param identifier The {@link FileIdentifier identifier} for the file.
	 * @return {@code true} if there is an instance, {@code false} otherwise
	 */
	protected static final boolean hasInstance(FileIdentifier<?> identifier) {
		return idMap.containsKey(identifier);
	}

	/**
	 * Checks whether there is already an instance.
	 *
	 * @param path The path pointing to the file.
	 * @return {@code true} if there is an instance, {@code false} otherwise
	 */
	public static final boolean hasInstance(Path path) {
		return pathMap.containsKey(path);
	}

	public static List<IFileManager<?>> getInstanceList(Path path) {
		return pathMap.get(path);
	}

	/**
	 * Removes an instance of a {@link IFileManager} for a certain file.
	 *
	 * @param identifier The {@link FileIdentifier identifier} for the file.
	 *
	 * @return The manager instance for the specified file, or {@code null} if no instance was created yet.
	 *
	 * @throws ClassCastException When the found instance is no subclass of R.
	 */
	@SuppressWarnings("unchecked")
	@CheckForNull
	protected static final <R extends IFileManager<?>> R removeInstance(FileIdentifier<?> identifier) {
		final List<IFileManager<?>> managerList = pathMap.get(identifier.getPath());
		if (managerList != null) {
			managerList.remove(identifier);
			if (managerList.isEmpty()) {
				pathMap.remove(identifier.getPath());
			}
		}
		return (R) idMap.remove(identifier);
	}

	protected static final <T> FileHandler<T> getFileHandler(Path path, ObjectCreator<T> objectCreator) {
		final FileHandler<T> fileHandler = new FileHandler<>(path, null, null);
		final String content = fileHandler.getContent();

		if (content != null) {
			final String fileName = path.getFileName().toString();
			final IPersistentFormat<T> format = objectCreator.formatManager.getFormatByContent(content, fileName);
			if (format == null) {
				fileHandler.getLastProblems().add(new Problem(new FormatManager.NoSuchExtensionException("No format found for file \"" + fileName + "\"!")));
			} else {
				try {
					final T object = objectCreator.createObject(path, format);
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

	/**
	 * Creates an instance of a {@link IFileManager} for a certain file.
	 *
	 * @param path The path pointing to the file.
	 * @param objectCreator Provides a corresponding content object for the file manager.
	 *
	 * @return The manager instance for the specified file, or {@code null} if no instance was created yet.
	 *
	 * @throws ClassCastException When the found instance is no subclass of R.
	 */
	@SuppressWarnings("unchecked")
	@CheckForNull
	protected static final <T, R extends IFileManager<T>> R newInstance(Path path, ObjectCreator<T> objectCreator) {
		final SimpleFileHandler<T> fileHandler = getFileHandler(path, objectCreator);
		if (fileHandler.getObject() != null) {
			try {
				final FileIdentifier<T> fileIdentifier = new FileIdentifier<T>(path, fileHandler.getFormat());

				final Constructor<? extends IFileManager<T>> constructor =
					objectCreator.fileManagerClass.getDeclaredConstructor(objectCreator.objectClass, FileIdentifier.class);
				constructor.setAccessible(true);
				final IFileManager<?> instance = constructor.newInstance(fileHandler.getObject(), fileIdentifier);

				idMap.put(fileIdentifier, instance);
				List<IFileManager<?>> managerlist = pathMap.get(path);
				if (managerlist == null) {
					managerlist = new LinkedList<>();
					pathMap.put(path, managerlist);
				}
				managerlist.add(instance);

				instance.getLastProblems().addAll(fileHandler.getLastProblems());
				return (R) objectCreator.fileManagerClass.cast(instance);
			} catch (ReflectiveOperationException | SecurityException | IllegalArgumentException e) {
				Logger.logError(e);
			}
		}
		return null;
	}

	/**
	 * Returns an instance of a {@link IFileManager} for a certain file. If no previous instance is available, this method creates a new one using
	 * {@link #newInstance(Path, ObjectCreator)}.
	 *
	 * @param identifier The {@link FileIdentifier identifier} for the file.
	 * @param objectCreator Provides a corresponding content object for the file manager.
	 * @param createInstance Whether a new instance should be created, if none is available.
	 *
	 * @return The manager instance for the specified file, or {@code null} if no instance is available and no new instance could be created.
	 *
	 * @throws ClassCastException When the found instance is no subclass of R.
	 */
	@SuppressWarnings("unchecked")
	@CheckForNull
	protected static final <T, R extends IFileManager<T>> R getInstance(Path path, ObjectCreator<T> objectCreator, boolean createInstance) {
		final IPersistentFormat<T> format = objectCreator.formatManager.getFormatByContent(path);
		if (format != null) {
			final IFileManager<?> instance = idMap.get(new FileIdentifier<T>(path, format));
			if (instance == null) {
				if (createInstance) {
					return newInstance(path, objectCreator);
				}
			} else if (objectCreator.fileManagerClass.isInstance(instance)) {
				return (R) objectCreator.fileManagerClass.cast(instance);
			}
		}
		return null;
	}

	private final IEventManager eventManager = new DefaultEventManager();
	private final ProblemList lastProblems = new ProblemList();

	protected final Object syncObject = new Object();

	protected final FileIdentifier<T> identifier;

	protected String persistentObjectSource;
	protected T persistentObject;
	protected T variableObject;

	private boolean modifying = false;

	protected AFileManager(T object, FileIdentifier<T> identifier) {
		this.identifier = identifier;

		variableObject = object;

		if (FileSystem.exists(identifier.getPath())) {
			try {
				final String content = new String(FileSystem.read(identifier.getPath()), DEFAULT_CHARSET);
				final ProblemList problems = identifier.getFormat().getInstance().read(variableObject, content);
				if (problems != null) {
					lastProblems.addAll(problems);
				}
			} catch (final Exception e) {
				handleException(e);
			}
		}
		setPersistentObject(copyObject(variableObject));
	}

	@Override
	public void addListener(IEventListener listener) {
		eventManager.addListener(listener);
	}

	protected abstract T copyObject(T oldObject);

	@Override
	public T getObject() {
		synchronized (syncObject) {
			return persistentObject;
		}
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
		return identifier.format;
	}

	@Override
	public ProblemList getLastProblems() {
		return lastProblems;
	}

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
	}

	protected void setPersistentObject(T persistentObject) {
		this.persistentObject = persistentObject;
		if (persistentObject == null) {
			persistentObjectSource = null;
		} else {
			persistentObjectSource = identifier.getFormat().getInstance().write(persistentObject);
		}
	}

	@Override
	public boolean read() {
		if (!FileSystem.exists(identifier.getPath())) {
			return false;
		}
		final boolean success, changed;
		synchronized (syncObject) {
			if (modifying) {
				return true;
			}
			lastProblems.clear();
			final T tempObject = copyObject(persistentObject);
			try {
				final String content = new String(FileSystem.read(identifier.getPath()), DEFAULT_CHARSET);
				final List<Problem> problemList = identifier.getFormat().getInstance().read(tempObject, content);
				if (problemList != null) {
					lastProblems.addAll(problemList);
				}
				changed = hasChanged(tempObject);
			} catch (final Exception e) {
				handleException(e);
				return false;
			}
			if (changed) {
				setPersistentObject(tempObject);
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
			final String write = identifier.getFormat().getInstance().write(persistentObject);
			identifier.getFormat().getInstance().read(variableObject, write);
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
	 * Compares the persistent with the given object for equality.<br/> Subclasses could override this method.
	 *
	 * @param newObject The given object.
	 * @return {@code true} if objects differ, {@code false} otherwise.
	 */
	protected boolean hasChanged(T newObject) {
		return !Objects.equals(identifier.getFormat().getInstance().write(newObject), persistentObjectSource);
	}

	/**
	 * Compares the persistent with the variable object for equality.<br/> Uses {@link #hasChanged(T)}.
	 *
	 * @return {@code true} if objects differ, {@code false} otherwise.
	 */
	@Override
	public boolean hasChanged() {
		return hasChanged(variableObject);
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
				FileSystem.write(identifier.getPath(), identifier.getFormat().getInstance().write(tempObject).getBytes(DEFAULT_CHARSET));
				setPersistentObject(copyObject(tempObject));
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
				setPersistentObject(copyObject(tempObject));
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
		removeInstance(identifier);
		synchronized (syncObject) {
			setPersistentObject(null);
			variableObject = null;
		}
	}

	@Override
	public String getAbsolutePath() {
		return identifier.getPath().toString();
	}

	@Override
	public Path getPath() {
		return identifier.path;
	}

	@Override
	public String toString() {
		return "File manager for " + identifier;
	}

}
