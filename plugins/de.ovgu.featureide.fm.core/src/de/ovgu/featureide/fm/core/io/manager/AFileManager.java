/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.event.DefaultEventManager;
import de.ovgu.featureide.fm.core.base.event.FeatureModelEvent;
import de.ovgu.featureide.fm.core.base.event.IEventManager;
import de.ovgu.featureide.fm.core.base.event.IFeatureModelListener;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;

/**
 * Responsible to load and save all information from / to a file.
 * 
 * @author Sebastian Krieter
 */
public abstract class AFileManager<T> implements IFileManager, IEventManager, IResourceChangeListener {

	private final IEventManager eventManager = new DefaultEventManager();

	private final List<Problem> lastProblems = new LinkedList<>();

	private final Object syncObject = new Object();

	protected final IPersistentFormat<T> format;

	protected final String absolutePath;
	protected final Path path;

	private final IPath eclipseFile;

	protected T persistentObject;
	protected T variableObject;

	private boolean saveFlag = false;

	public IPersistentFormat<T> getFormat() {
		return format;
	}

	protected AFileManager(String absolutePath, IPersistentFormat<T> format) {
		this.format = format;
		this.absolutePath = absolutePath;
		path = Paths.get(absolutePath);

		persistentObject = null;
		variableObject = null;

		eclipseFile = new org.eclipse.core.runtime.Path(absolutePath);
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this, IResourceChangeEvent.POST_CHANGE);
	}

	public void init() {
		if (persistentObject == null && !read()) {
			persistentObject = createNewObject();
			variableObject = copyObject(persistentObject);
		}
	}

	public T getObject() {
		return persistentObject;
	}

	public T editObject() {
		return variableObject;
	}

	public List<Problem> getLastProblems() {
		return lastProblems;
	}

	public synchronized boolean read() {
		if (!Files.exists(path)) {
			return false;
		}
		lastProblems.clear();
		try {
			final T newObject = createNewObject();

			final String content = new String(Files.readAllBytes(path), Charset.availableCharsets().get("UTF-8"));
			List<Problem> problemList = format.getInstance().read(newObject, content);
			if (problemList != null) {
				lastProblems.addAll(problemList);
			}

			synchronized (syncObject) {
				persistentObject = newObject;
				variableObject = copyObject(newObject);
			}

			fireEvent(new FeatureModelEvent(persistentObject, FeatureModelEvent.MODEL_DATA_LOADED));
		} catch (Exception e) {
			handleException(e);
		}
		return lastProblems.isEmpty();
	}

	protected abstract T createNewObject();

	protected abstract T copyObject(T oldObject);

	public boolean save() {
		lastProblems.clear();
		try {
			synchronized (syncObject) {
				saveFlag = true;
			}
			final byte[] content = format.getInstance().write(variableObject).getBytes(Charset.availableCharsets().get("UTF-8"));
			Files.write(path, content, StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING, StandardOpenOption.WRITE);

			synchronized (syncObject) {
				persistentObject = variableObject;
				variableObject = copyObject(persistentObject);
			}

			fireEvent(new FeatureModelEvent(persistentObject, FeatureModelEvent.MODEL_DATA_SAVED));
		} catch (Exception e) {
			handleException(e);
		}
		return lastProblems.isEmpty();
	}

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
		FMCorePlugin.getDefault().logError(e);
	}

	@Override
	public void addListener(IFeatureModelListener listener) {
		eventManager.addListener(listener);
	}

	@Override
	public void fireEvent(FeatureModelEvent event) {
		eventManager.fireEvent(event);
	}

	@Override
	public void removeListener(IFeatureModelListener listener) {
		eventManager.removeListener(listener);
	}

	@Override
	public void resourceChanged(IResourceChangeEvent event) {
		final IResourceDelta member = event.getDelta().findMember(eclipseFile);
		if (member != null) {
			synchronized (syncObject) {
				if (saveFlag) {
					saveFlag = false;
				} else {
					read();
				}
			}
		}
	}

	public void dispose() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
		FileManagerMap.remove(absolutePath);

		persistentObject = null;
		variableObject = null;
	}

	@Override
	public String getAbsolutePath() {
		return absolutePath;
	}

	@Override
	public String toString() {
		return "File manager for " + absolutePath;
	}

}
