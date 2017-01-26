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
import java.nio.charset.Charset;
import java.nio.file.Files;
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
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Responsible to load and save all information from / to a file.<br/>
 * To get an instance use the {@link FileManagerMap}.
 * 
 * @author Sebastian Krieter
 */
public abstract class AFileManager<T> implements IFileManager, IEventManager {

	protected static abstract class ObjectCreator<T> {
		private final Class<T> objectClass;
		private final Class<? extends AFileManager<T>> fileManagerClass;
		private final FormatManager<? extends IPersistentFormat<T>> formatManager;

		public ObjectCreator(Class<T> objectClass, Class<? extends AFileManager<T>> fileManagerClass,
				FormatManager<? extends IPersistentFormat<T>> formatManager) {
			this.objectClass = objectClass;
			this.fileManagerClass = fileManagerClass;
			this.formatManager = formatManager;
		}

		protected abstract T createObject(Path path, final IPersistentFormat<T> format) throws NoSuchExtensionException;
	}

	public static final Charset DEFAULT_CHARSET = Charset.forName("UTF-8");

	protected static final Map<String, IFileManager> map = new HashMap<>();

	protected static final String constructAbsolutePath(Path path) {
		final Path p = path.toAbsolutePath();
		final String absolutePath = p.toString();
		return absolutePath;
	}

	public static final String constructExtraPath(String path, IPersistentFormat<?> format) throws IllegalArgumentException {
		final Path mainPath = Paths.get(path).toAbsolutePath();
		final Path mainFileNamePath = mainPath.getFileName();
		if (mainFileNamePath != null) {
			final String mainFileNameString = mainFileNamePath.toString();
			final Path subpath = mainPath.subpath(0, mainPath.getNameCount() - 1);
			final Path root = mainPath.getRoot();
			if (subpath != null && root != null) {
				final Path extraFolder = root.resolve(subpath.resolve("." + mainFileNameString));

				if (!Files.exists(extraFolder)) {
					try {
						Files.createDirectory(extraFolder);
					} catch (IOException e) {
						Logger.logError(e);
					}
				}

				return extraFolder.resolve(mainFileNameString + "." + format.getSuffix()).toString();
			}
		}
		throw new IllegalArgumentException("Path " + path + " can not be transformed.");
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
					final T featureModel = objectCreator.createObject(path, format);
					fileHandler.setObject(featureModel);
					fileHandler.setFormat(format);
					fileHandler.parse(content);
				} catch (NoSuchExtensionException e) {
					fileHandler.getLastProblems().add(new Problem(e));
				}
			}
		}

		return fileHandler;
	}

	@CheckForNull
	protected static final <T> IFileManager newAInstance(Path path, ObjectCreator<T> objectCreator) {
		final String absolutePath = constructAbsolutePath(path);
		final SimpleFileHandler<T> fileHandler = getFileHandler(path, objectCreator);

		try {
			final Constructor<? extends AFileManager<T>> constructor = objectCreator.fileManagerClass.getDeclaredConstructor(objectCreator.objectClass,
					String.class, IPersistentFormat.class);
			constructor.setAccessible(true);
			final IFileManager instance = constructor.newInstance(fileHandler.getObject(), absolutePath, fileHandler.getFormat());
			map.put(absolutePath, instance);
			instance.getLastProblems().addAll(fileHandler.getLastProblems());
			return objectCreator.fileManagerClass.cast(instance);
		} catch (ReflectiveOperationException | SecurityException | IllegalArgumentException e) {
			Logger.logError(e);
			return null;
		}
	}

	@CheckForNull
	protected static final <T> IFileManager getAInstance(Path path, ObjectCreator<T> objectCreator) {
		final IFileManager instance = getAInstance(path);
		if (instance == null) {
			return newAInstance(path, objectCreator);
		} else if (objectCreator.fileManagerClass.isInstance(instance)) {
			return objectCreator.fileManagerClass.cast(instance);
		} else {
			return null;
		}
	}

	@CheckForNull
	protected static final IFileManager getAInstance(Path path) {
		return map.get(constructAbsolutePath(path));
	}

	/**
	 * Checks whether there is already instance.
	 * 
	 * @param path
	 * @return
	 */
	public static final boolean hasInstance(Path path) {
		return map.containsKey(constructAbsolutePath(path));
	}

	public static final IFileManager removeInstance(Path path) {
		return map.remove(constructAbsolutePath(path));
	}

	private final IEventManager eventManager = new DefaultEventManager();
	private final ProblemList lastProblems = new ProblemList();

	private final Object syncObject = new Object();

	private final Object saveSyncObject = new Object();
	protected final IPersistentFormat<T> format;

	protected final String absolutePath;
	protected final Path path;

	protected T persistentObject;

	protected T variableObject;

	protected AFileManager(T object, String absolutePath, IPersistentFormat<T> format) {
		this.format = format;
		this.absolutePath = absolutePath;
		path = Paths.get(absolutePath);

		variableObject = object;
		persistentObject = copyObject(variableObject);
	}

	@Override
	public void addListener(IEventListener listener) {
		eventManager.addListener(listener);
	}

	protected abstract T copyObject(T oldObject);

	@Override
	public void dispose() {
		removeInstance(Paths.get(absolutePath));

		persistentObject = null;
		variableObject = null;
	}

	public T editObject() {
		synchronized (saveSyncObject) {
			return variableObject;
		}
	}

	@Override
	public void fireEvent(FeatureIDEEvent event) {
		eventManager.fireEvent(event);
	}

	@Override
	public String getAbsolutePath() {
		return absolutePath;
	}

	public IPersistentFormat<T> getFormat() {
		return format;
	}

	public ProblemList getLastProblems() {
		return lastProblems;
	}

	public T getObject() {
		synchronized (syncObject) {
			return persistentObject;
		}
	}

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
	}

	/**
	 * Copy on write.
	 */
	protected void persist() {
		synchronized (syncObject) {
			persistentObject = copyObject(variableObject);
		}
	}

	public boolean read() {
		if (!FileSystem.exists(path)) {
			return false;
		}
		lastProblems.clear();
		try {
			final String content = new String(FileSystem.read(path), DEFAULT_CHARSET);
			List<Problem> problemList;
			synchronized (saveSyncObject) {
				problemList = format.getInstance().read(variableObject, content);
			}
			if (problemList != null) {
				lastProblems.addAll(problemList);
			}
			persist();
			fireEvent(new FeatureIDEEvent(persistentObject, EventType.MODEL_DATA_LOADED));
		} catch (Exception e) {
			handleException(e);
		}
		return lastProblems.isEmpty();
	}

	@Override
	public void removeListener(IEventListener listener) {
		eventManager.removeListener(listener);
	}

	public boolean save() {
		lastProblems.clear();
		try {
			final byte[] content = format.getInstance().write(variableObject).getBytes(DEFAULT_CHARSET);
			synchronized (saveSyncObject) {
				FileSystem.write(path, content);
			}
			persist();
			fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_SAVED));
		} catch (Exception e) {
			handleException(e);
		}
		return lastProblems.isEmpty();
	}

	@Override
	public String toString() {
		return "File manager for " + absolutePath;
	}

}
