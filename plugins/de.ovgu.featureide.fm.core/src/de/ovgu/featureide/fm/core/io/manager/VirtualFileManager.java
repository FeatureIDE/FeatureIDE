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

import de.ovgu.featureide.fm.core.functional.Functional.ICriticalConsumer;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Holds a virtual object.
 *
 * @author Sebastian Krieter
 */
public class VirtualFileManager<T> extends AFileManager<T> {

	public static class ObjectCreator<T> extends AFileManager.ObjectCreator<T> {

		private final T object;

		public ObjectCreator(T object) {
			this.object = object;
		}

		@Override
		protected T createObject() {
			return object;
		}

		@Override
		protected Snapshot<T> createSnapshot(T object) {
			return new Snapshot<>(object);
		}

	}

	public VirtualFileManager(T object, IPersistentFormat<T> format) {
		super(format, VirtualFileManager.class.getName() + object.hashCode(), object, new ObjectCreator<>(object));
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
	public boolean externalSave(ICriticalConsumer<T> externalSaveMethod) {
		return true;
	}

	@Override
	public Path getPath() {
		return null;
	}

	@Override
	public ProblemList getLastProblems() {
		return new ProblemList();
	}

	@Override
	public String toString() {
		return "Virtual File manager for " + variableObject;
	}

}
