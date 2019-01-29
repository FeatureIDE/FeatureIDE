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

import java.lang.reflect.Constructor;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.event.DefaultEventManager;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.event.IEventManager;
import de.ovgu.featureide.fm.core.base.impl.FactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.io.ExternalChangeListener;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Responsible to load and save all information from / to a file.
 *
 * @author Sebastian Krieter
 */
public abstract class AFileManager<T> implements IFileManager<T> {

	public static final Charset DEFAULT_CHARSET = Charset.forName("UTF-8");

	protected static final Map<Path, IFileManager<?>> pathMap = new HashMap<>();

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
				return root.resolve(subpath.resolve(".featureide").resolve(mainFileNameString)).resolve(mainFileNameString + "." + format.getSuffix());
			}
		}
		throw new IllegalArgumentException("Path " + path + " can not be transformed.");
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
	public static final <T, R extends IFileManager<T>> R removeInstance(Path identifier, Class<R> fileManagerClass) {
		synchronized (pathMap) {
			if (getInstance(identifier, false, fileManagerClass) != null) {
				return (R) pathMap.remove(identifier);
			} else {
				return null;
			}
		}
	}

	/**
	 * Returns an instance of a {@link IFileManager} for a certain file. If no previous instance is available, this method creates a new one using
	 * a constructor with only a {@link Path} parameter.
	 *
	 * @param path The Path to the corresponding file.
	 * @param createInstance Whether a new instance should be created, if none is available.
	 * @param fileManagerClass Provides a corresponding content object for the file manager.
	 *
	 * @return The manager instance for the specified file, or {@code null} if no instance is available and no new instance could be created.
	 *
	 * @throws ClassCastException When the found instance is no subclass of R.
	 */
	@CheckForNull
	protected static <T, R extends IFileManager<T>> R getInstance(Path path, boolean createInstance, Class<R> fileManagerClass) {
		synchronized (pathMap) {
			final IFileManager<?> instance = pathMap.get(path);
			if (fileManagerClass.isInstance(instance)) {
				return (R) fileManagerClass.cast(instance);
			} else {
				if (createInstance && (path != null) && Files.exists(path)) {
					try {
						final Constructor<R> constructor = fileManagerClass.getDeclaredConstructor(Path.class);
						constructor.setAccessible(true);
						final R newInstance = constructor.newInstance(path);
						if (instance != null) {
							Logger.logWarning("Replaced file manager " + instance + " with " + newInstance + ".");
						}
						pathMap.put(path, newInstance);
						return newInstance;
					} catch (final Exception e) {
						Logger.logError(e);
					}
				}
			}
			return null;
		}
	}

	public static IFileManager<?> getInstance(Path path) {
		synchronized (pathMap) {
			return pathMap.get(path);
		}
	}

	private final IEventManager eventManager = new DefaultEventManager();
	private final ProblemList lastProblems = new ProblemList();

	protected final Lock fileOperationLock = new ReentrantLock();

	private final Path path;
	private final List<? extends IPersistentFormat<T>> formats;
	private final FactoryManager<T> factoryManager;

	protected String persistentObjectSource;
	protected T persistentObject;
	protected T variableObject;

	private IPersistentFormat<T> format;
	private boolean modifying = false;

	protected AFileManager(Path path, FormatManager<T> formatManager, FactoryManager<T> factoryManager) {
		this.path = path;
		formats = formatManager.getFormatListForExtension(getAbsolutePath());
		this.factoryManager = factoryManager;

		T newPersistentObject = null;
		if (FileSystem.exists(path)) {
			try {
				final String content = new String(FileSystem.read(path), DEFAULT_CHARSET);
				detectFormat(content);
				final ProblemList problems = format.getInstance().read(variableObject, content);
				newPersistentObject = createObject();
				format.getInstance().read(newPersistentObject, content);
				if (problems != null) {
					lastProblems.addAll(problems);
				}
			} catch (final Exception e) {
				handleException(e);
			}
		} else {
			// TODO use cases?
			try {
				format = formats.get(0);
				setVariableObject(createObject());
				newPersistentObject = createObject();
			} catch (final Exception e) {
				e.printStackTrace();
			}
		}
		setPersistentObject(newPersistentObject);
	}

	private void detectFormat(final CharSequence content) throws Exception {
		for (final IPersistentFormat<T> possibleFormat : formats) {
			if (possibleFormat.supportsContent(content)) {
				if (format != possibleFormat) {
					format = possibleFormat;
					setVariableObject(createObject());
				}
				break;
			}
		}
		if (format == null) {
			throw new NoSuchExtensionException("No fitting format found for file " + path.toString());
		}
	}

	protected void setVariableObject(T variableObject) {
		this.variableObject = variableObject;
	}

	protected T createObject() throws Exception {
		return factoryManager.getFactory(path, format).create();
	}

	@Override
	public void addListener(IEventListener listener) {
		eventManager.addListener(listener);
	}

	@Override
	public List<IEventListener> getListeners() {
		return eventManager.getListeners();
	}

	protected abstract T copyObject(T oldObject);

	@Override
	public T getObject() {
		return persistentObject;
	}

	@Override
	public T getSnapshot() {
		fileOperationLock.lock();
		try {
			return copyObject(variableObject);
		} finally {
			fileOperationLock.unlock();
		}
	}

	@Override
	public T editObject() {
		return variableObject;
	}

	@Override
	public Lock getFileOperationLock() {
		return fileOperationLock;
	}

	public void setModifying(boolean modifying) {
		fileOperationLock.lock();
		try {
			this.modifying = modifying;
		} finally {
			fileOperationLock.unlock();
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
		fileOperationLock.lock();
		try {
			return new ProblemList(lastProblems);
		} finally {
			fileOperationLock.unlock();
		}
	}

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
	}

	protected void setPersistentObject(T persistentObject) {
		this.persistentObject = persistentObject;
		if (persistentObject == null) {
			persistentObjectSource = null;
		} else {
			persistentObjectSource = format.getInstance().write(persistentObject);
		}
	}

	@Override
	public ProblemList read() {
		if (!FileSystem.exists(path)) {
			return new ProblemList(Arrays.asList(new Problem(new NoSuchFileException(path.toString()))));
		}
		if (persistentObject == null) {
			return new ProblemList(Arrays.asList(new Problem(new IllegalStateException("Initialization Problem"))));
		}
		final boolean changed;
		final ProblemList problems;
		fileOperationLock.lock();
		try {
			if (modifying) {
				return new ProblemList();
			}
			lastProblems.clear();
			final T tempObject;
			try {
				final String content = new String(FileSystem.read(path), DEFAULT_CHARSET);
				detectFormat(content);
				tempObject = createObject();
				final List<Problem> problemList = format.getInstance().read(tempObject, content);
				if (problemList != null) {
					lastProblems.addAll(problemList);
				}
				changed = hasChanged(tempObject);
			} catch (final Exception e) {
				handleException(e);
				return new ProblemList(lastProblems);
			}
			if (changed) {
				setPersistentObject(tempObject);
			}
			problems = new ProblemList(lastProblems);
		} finally {
			fileOperationLock.unlock();
		}
		if (changed) {
			ExternalChangeListener.update(this);
		}
		return problems;
	}

	@Override
	public ProblemList readFromSource(CharSequence source) {
		fileOperationLock.lock();
		try {
			lastProblems.clear();
			try {
				detectFormat(source);
				final List<Problem> problemList = format.getInstance().read(variableObject, source);
				if (problemList != null) {
					lastProblems.addAll(problemList);
				}
			} catch (final Exception e) {
				handleException(e);
			}
			return new ProblemList(lastProblems);
		} finally {
			fileOperationLock.unlock();
		}
	}

	// TODO Quickfix for #501. Should be implemented by overwriting the current instance pointer.
	@Override
	public void overwrite() {
		fileOperationLock.lock();
		try {
			if (modifying) {
				return;
			}
			final String write = format.getInstance().write(persistentObject);
			format.getInstance().read(variableObject, write);
		} finally {
			fileOperationLock.unlock();
		}
		fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_OVERWRITTEN));
	}

	@Override
	public void removeListener(IEventListener listener) {
		eventManager.removeListener(listener);
	}

	/**
	 * Compares the persistent with the given object for equality.<br> Subclasses could override this method.
	 *
	 * @param newObject The given object.
	 * @return {@code true} if objects differ, {@code false} otherwise.
	 */
	protected boolean hasChanged(T newObject) {
		return !Objects.equals(format.getInstance().write(newObject), persistentObjectSource);
	}

	/**
	 * Compares the persistent with the variable object for equality.<br> Uses {@link #hasChanged(Object)}.
	 *
	 * @return {@code true} if objects differ, {@code false} otherwise.
	 */
	@Override
	public boolean hasChanged() {
		return hasChanged(variableObject);
	}

	@Override
	public ProblemList save() {
		final ProblemList problems;
		fileOperationLock.lock();
		try {
			lastProblems.clear();
			try {
				if (modifying) {
					return new ProblemList();
				}
				modifying = true;
				final String source = format.getInstance().write(variableObject);
				FileSystem.write(path, source.getBytes(DEFAULT_CHARSET));
				final T tempObject = createObject();
				format.read(tempObject, source);
				setPersistentObject(tempObject);
			} catch (final Exception e) {
				handleException(e);
				return new ProblemList(lastProblems);
			} finally {
				modifying = false;
			}
			problems = new ProblemList(lastProblems);
		} finally {
			fileOperationLock.unlock();
		}
		fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_SAVED));
		return problems;
	}

	@Override
	public ProblemList externalSave(Runnable externalSaveMethod) {
		final ProblemList problems;
		fileOperationLock.lock();
		try {
			lastProblems.clear();
			try {
				if (modifying) {
					return new ProblemList();
				}
				modifying = true;
				externalSaveMethod.run();
				final List<Problem> problemList = read();
				if (problemList != null) {
					lastProblems.addAll(problemList);
				}
			} catch (final Exception e) {
				handleException(e);
				return new ProblemList(lastProblems);
			} finally {
				modifying = false;
			}
			problems = new ProblemList(lastProblems);
		} finally {
			fileOperationLock.unlock();
		}
		fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_SAVED));
		return problems;
	}

	@Override
	public void dispose() {
		synchronized (pathMap) {
			if (pathMap.get(path) == this) {
				pathMap.remove(path);
			}
		}
		fileOperationLock.lock();
		try {
			setPersistentObject(null);
			variableObject = null;
		} finally {
			fileOperationLock.unlock();
		}
	}

	@Override
	public String getAbsolutePath() {
		return path.toString();
	}

	@Override
	public Path getPath() {
		return path;
	}

	@Override
	public String toString() {
		return "File manager for " + path.toString();
	}

}
