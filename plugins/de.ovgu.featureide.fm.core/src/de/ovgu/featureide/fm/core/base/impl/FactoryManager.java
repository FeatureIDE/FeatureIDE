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
package de.ovgu.featureide.fm.core.base.impl;

import java.nio.file.Path;
import java.util.HashMap;

import de.ovgu.featureide.fm.core.ExtensionManager;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFactory;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Returns custom factories to create instances of T.
 *
 * @author Sebastian Krieter
 */
public abstract class FactoryManager<T> extends ExtensionManager<IFactory<T>> {

	protected abstract String getDefaultID();

	private IFactoryWorkspaceLoader fwIOHandler = null;

	public final void setWorkspaceLoader(IFactoryWorkspaceLoader factorySpaceLoader) {
		fwIOHandler = factorySpaceLoader != null ? factorySpaceLoader : new CoreFactoryWorkspaceLoader();
		if (!load()) {
			try {
				getDefaultFactoryWorkspace().setDefaultFactoryID(getFactory(getDefaultID()).getId());
			} catch (final de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException e) {
				Logger.logError(e);
			}
		}
	}

	protected final HashMap<Path, FactoryWorkspace> projectMap = new HashMap<>();
	protected final FactoryWorkspace defaultWorkspace = new FactoryWorkspace();

	public FactoryWorkspace getFactoryWorkspace(Path path) {
		final FactoryWorkspace factoryWorkspace = projectMap.get(fwIOHandler.getDistinctPath(path));
		return factoryWorkspace != null ? factoryWorkspace : defaultWorkspace;
	}

	public FactoryWorkspace getDefaultFactoryWorkspace() {
		return defaultWorkspace;
	}

	public FactoryWorkspace addFactoryWorkspace(Path path) {
		final Path distinctPath = fwIOHandler.getDistinctPath(path);
		FactoryWorkspace factoryWorkspace = getFactoryWorkspace(distinctPath);
		if (factoryWorkspace == null) {
			factoryWorkspace = defaultWorkspace.clone();
			projectMap.put(distinctPath, factoryWorkspace);
		}
		return factoryWorkspace;
	}

	public void removeFactoryWorkspace(Path path) {
		projectMap.remove(fwIOHandler.getDistinctPath(path));
	}

	/**
	 * Returns a specific factory associated with the string <b>id</b>.
	 *
	 * @param id the (unique) identifier for an instance of {@link IFactory} to be returned
	 * @return An instance of the factory associated with <b>id</b>, or throws a {@link NoSuchExtensionException} in case <b>id</b> is not associated with any
	 *         factory.
	 * @throws NoSuchExtensionException If no factory with the given ID is registered.
	 */
	public IFactory<? extends T> getFactory(String id) throws NoSuchExtensionException {
		return getExtension(id);
	}

	/**
	 * Returns the factory that was used to create the given object. (if the factory is not available the default factory is returned).
	 *
	 * @param object the object
	 *
	 * @return Returns the factory for the given object.
	 */
	public abstract IFactory<? extends T> getFactory(T object);

	/**
	 * Returns the factory for the given path and format. (if none is specified an instance of the default factory is returned).
	 *
	 * @param path
	 * @param format
	 *
	 * @return Returns the feature model factory for a certain path and format.
	 *
	 * @throws NoSuchExtensionException
	 */
	public IFactory<? extends T> getFactory(Path path, IPersistentFormat<? extends T> format) throws NoSuchExtensionException {
		final FactoryWorkspace factoryWorkspace = getFactoryWorkspace(path);
		return getFactory(factoryWorkspace.getID(format));
	}

	/**
	 * Returns the currently set default factory for the given format (if none is specified an instance of the default factory is returned).<br/> <br/>
	 * <b>Important Note:</b> If possible, use {@link #getFactory(String, IPersistentFormat)} or {@link #getFactory(T)} instead to
	 * ensure that the correct factory is used for the underlying feature model file.
	 *
	 * @param format
	 *
	 * @return Returns the default factory for a certain format.
	 *
	 * @throws NoSuchExtensionException
	 */
	public IFactory<? extends T> getFactory(IPersistentFormat<? extends T> format) throws NoSuchExtensionException {
		return getFactory(getDefaultFactoryWorkspace().getID(format));
	}

	public boolean load() {
		return fwIOHandler.load(this);
	}

	public void save() {
		fwIOHandler.save(this);
	}
}
