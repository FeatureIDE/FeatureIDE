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

import java.nio.charset.Charset;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import de.ovgu.featureide.fm.core.base.event.DefaultEventManager;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.event.IEventManager;
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

	private final Object syncObject = new Object();
	private final Object saveSyncObject = new Object();

	protected final IPersistentFormat<T> format;

	protected final String absolutePath;
	protected final Path path;

	protected T persistentObject;
	protected T variableObject;

	public IPersistentFormat<T> getFormat() {
		return format;
	}

	protected AFileManager(T object, String absolutePath, IPersistentFormat<T> format) {
		this.format = format;
		this.absolutePath = absolutePath;
		path = Paths.get(absolutePath);

		variableObject = object;
		persistentObject = copyObject(variableObject);
	}

	public T getObject() {
		synchronized (syncObject) {
			return persistentObject;
		}
	}

	public void setObject(T object) {
		synchronized (syncObject) {
			variableObject = object;
			persist();
		}
	}

	public T editObject() {
		synchronized (saveSyncObject) {
			return variableObject;
		}
	}

	public ProblemList getLastProblems() {
		return lastProblems;
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

	/**
	 * Copy on write.
	 */
	protected void persist() {
		synchronized (syncObject) {
			persistentObject = copyObject(variableObject);
		}
	}

	protected abstract T copyObject(T oldObject);

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

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
	}

	@Override
	public void addListener(IEventListener listener) {
		eventManager.addListener(listener);
	}

	@Override
	public void fireEvent(FeatureIDEEvent event) {
		eventManager.fireEvent(event);
	}

	@Override
	public void removeListener(IEventListener listener) {
		eventManager.removeListener(listener);
	}

	@Override
	public void dispose() {
		FileManagerMap.remove(absolutePath);

		persistentObject = null;
		variableObject = null;
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
