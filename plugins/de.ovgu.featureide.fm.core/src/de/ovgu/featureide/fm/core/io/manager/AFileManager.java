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

import java.nio.charset.Charset;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import de.ovgu.featureide.fm.core.base.event.DefaultEventManager;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.event.IEventManager;
import de.ovgu.featureide.fm.core.io.ExternalChangeListener;
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
public abstract class AFileManager<T> implements IFileManager<T>, IEventManager {

	public static final Charset DEFAULT_CHARSET = Charset.forName("UTF-8");

	private final IEventManager eventManager = new DefaultEventManager();

	private final ProblemList lastProblems = new ProblemList();

	protected final Object syncObject = new Object();

	protected final IPersistentFormat<T> format;

	protected final String absolutePath;
	protected final Path path;

	protected T persistentObject;
	protected T variableObject;
	protected T localObject;
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
			} catch (Exception e) {
				handleException(e);
			}
		}
		persistentObject = copyObject(variableObject);
		localObject = copyObject(variableObject);
	}

	@Override
	public void addListener(IEventListener listener) {
		eventManager.addListener(listener);
	}

	protected abstract T copyObject(T oldObject);

	public T getObject() {
		return persistentObject;
	}

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

	public IPersistentFormat<T> getFormat() {
		return format;
	}

	public ProblemList getLastProblems() {
		return lastProblems;
	}

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
	}

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
				changed = !compareObjects(tempObject, localObject);
			} catch (Exception e) {
				handleException(e);
				return false;
			}
			if (changed) {
				localObject = tempObject;
			}
			success = lastProblems.isEmpty();
		}
		if (changed) {
			ExternalChangeListener.update(this);
		}
		return success;
	}

	// TODO Quickfix for #501. Should be implemented by overriding the current instance pointer.
	public void override() {
		synchronized (syncObject) {
			if (modifying) {
				return;
			}
			final String write = format.getInstance().write(localObject);
			format.getInstance().read(variableObject, write);
			format.getInstance().read(persistentObject, write);
			//			variableObject = copyObject(localObject);
			//			persistentObject = copyObject(localObject);
		}
		fireEvent(new FeatureIDEEvent(variableObject, EventType.MODEL_DATA_OVERRIDDEN));
	}

	@Override
	public void removeListener(IEventListener listener) {
		eventManager.removeListener(listener);
	}

	/**
	 * Compares two object for equality.<br/>
	 * Subclasses should override (implement) this method.
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
				localObject = copyObject(tempObject);
			} catch (Exception e) {
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
				localObject = copyObject(tempObject);
			} catch (Exception e) {
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
		FileManagerMap.remove(absolutePath);
		synchronized (syncObject) {
			persistentObject = null;
			variableObject = null;
			localObject = null;
		}
	}

	@Override
	public String getAbsolutePath() {
		return absolutePath;
	}

	public Path getPath() {
		return path;
	}

	@Override
	public String toString() {
		return "File manager for " + absolutePath;
	}

}
