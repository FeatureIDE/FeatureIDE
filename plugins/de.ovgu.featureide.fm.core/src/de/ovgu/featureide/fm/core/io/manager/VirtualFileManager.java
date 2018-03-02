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

import de.ovgu.featureide.fm.core.base.event.DefaultEventManager;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.event.IEventManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Holds a virtual object.
 *
 * @author Sebastian Krieter
 */
public class VirtualFileManager<T> implements IFileManager<T>, IEventManager {

	private final IEventManager eventManager = new DefaultEventManager();

	protected T variableObject;

	protected final IPersistentFormat<T> format;

	public VirtualFileManager(T object, IPersistentFormat<T> format) {
		this.format = format;
		variableObject = object;
	}

	@Override
	public IPersistentFormat<T> getFormat() {
		return format;
	}

	@Override
	public T getObject() {
		return variableObject;
	}

	@Override
	public T editObject() {
		return variableObject;
	}

	@Override
	public ProblemList getLastProblems() {
		return new ProblemList();
	}

	@Override
	public boolean read() {
		return true;
	}

	@Override
	public void override() {}

	@Override
	public boolean save() {
		return true;
	}

	@Override
	public boolean externalSave(Runnable externalSaveMethod) {
		return true;
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
		variableObject = null;
	}

	@Override
	public String getAbsolutePath() {
		return "";
	}

	@Override
	public Path getPath() {
		return null;
	}

	@Override
	public String toString() {
		return "Virtual File manager for " + variableObject;
	}

	@Override
	public boolean hasChanged() {
		return false;
	}

}
