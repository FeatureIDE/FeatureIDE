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
import java.nio.file.Paths;

import de.ovgu.featureide.fm.core.base.event.DefaultEventManager;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.event.IEventManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Responsible to load and save all information from / to a file.<br/> To get an instance use the {@link FileManagerMap}.
 *
 * @author Sebastian Krieter
 */
public abstract class AFileManager<T> implements IFileManager<T>, IEventManager {

	public static abstract class ObjectCreator<T> {

		protected IPersistentFormat<T> format;
		protected Path path;

		protected void setPath(Path path, IPersistentFormat<T> format) throws Exception {
			this.path = path;
			this.format = format;
		}

		protected abstract T createObject();

		protected abstract Snapshot<T> createSnapshot(T object);

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
	}

	protected final ObjectCreator<T> objectCreator;
	protected final IPersistentFormat<T> format;
	protected final String absolutePath;

	protected Snapshot<T> persistentObject;
	protected T variableObject;

	private final IEventManager eventManager = new DefaultEventManager();

	public AFileManager(IPersistentFormat<T> format, String absolutePath, T variableObject, ObjectCreator<T> objectCreator) {
		this.format = format;
		this.absolutePath = absolutePath;
		this.variableObject = variableObject;
		this.objectCreator = objectCreator;
		this.persistentObject = objectCreator.createSnapshot(variableObject);
	}

	@Override
	public void dispose() {
		FileManagerMap.removeInstance(Paths.get(absolutePath));
		synchronized (this) {
			persistentObject = null;
			variableObject = null;
		}
	}

	@Override
	public void addListener(IEventListener listener) {
		eventManager.addListener(listener);
	}

	@Override
	public void removeListener(IEventListener listener) {
		eventManager.removeListener(listener);
	}

	@Override
	public void fireEvent(FeatureIDEEvent event) {
		eventManager.fireEvent(event);
	}

	// TODO !!! setfeaturemodel method for configuration
	@Override
	public void setObject(T object) {
		synchronized (this) {
			variableObject = object;
			persistentObject = objectCreator.createSnapshot(variableObject);
		}
	}

	@Override
	public T getObject() {
		return persistentObject.getObject();
	}

	@Override
	public T editObject() {
		return variableObject;
	}

	@Override
	public Snapshot<T> getSnapshot() {
		return persistentObject;
	}

	@Override
	public IPersistentFormat<T> getFormat() {
		return format;
	}

	@Override
	public String getAbsolutePath() {
		return absolutePath;
	}

}
