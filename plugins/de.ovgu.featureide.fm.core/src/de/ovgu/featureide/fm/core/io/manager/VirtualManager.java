/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.function.Consumer;
import java.util.function.Function;

import de.ovgu.featureide.fm.core.base.event.DefaultEventManager;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.event.IEventManager;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Operates on a predefined object. Does not interact with the file system.
 *
 * @author Sebastian Krieter
 */
public class VirtualManager<T> implements IManager<T> {

	private final IEventManager eventManager = new DefaultEventManager();

	protected final T variableObject;

	protected final Lock lock = new ReentrantLock();

	public VirtualManager(T object) {
		variableObject = object;
	}

	@Override
	public T getObject() {
		return variableObject;
	}

	@Override
	public T getVarObject() {
		return variableObject;
	}

	@Override
	public <R> R processObject(Function<T, R> editOperation) {
		return processObject(editOperation, true);
	}

	@Override
	public <R> R processObject(Function<T, R> editOperation, boolean edit) {
		lock.lock();
		try {
			return editOperation.apply(variableObject);
		} finally {
			lock.unlock();
		}
	}

	@Override
	public void editObject(Consumer<T> editOperation) {
		lock.lock();
		try {
			editOperation.accept(variableObject);
		} finally {
			lock.unlock();
		}
	}

	@Override
	public void addListener(IEventListener listener) {
		eventManager.addListener(listener);
	}

	@Override
	public List<IEventListener> getListeners() {
		return eventManager.getListeners();
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
	public String toString() {
		return "Virtual File manager for " + variableObject;
	}

	@Override
	public boolean hasChanged() {
		return false;
	}

	@Override
	public Lock getFileOperationLock() {
		return lock;
	}

	@Override
	public T getSnapshot() {
		return variableObject;
	}

	@Override
	public ProblemList externalSave(Runnable externalSaveMethod) {
		lock.lock();
		try {
			try {
				externalSaveMethod.run();
			} catch (final Exception e) {
				return new ProblemList(Arrays.asList(new Problem(e)));
			}
		} finally {
			lock.unlock();
		}
		return new ProblemList();
	}

	@Override
	public void dispose() {}

	@Override
	public void overwrite() {}

}
