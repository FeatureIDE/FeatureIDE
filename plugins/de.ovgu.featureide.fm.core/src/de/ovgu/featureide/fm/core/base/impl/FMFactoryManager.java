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
package de.ovgu.featureide.fm.core.base.impl;

import de.ovgu.featureide.fm.core.CoreExtensionLoader;
import de.ovgu.featureide.fm.core.ExtensionManager;
import de.ovgu.featureide.fm.core.IExtensionLoader;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Returns custom factories to create {@link IFeatureModel}, {@link IFeature}, and {@link IConstraint} instances.
 *
 * @author Sebastian Krieter
 */
public final class FMFactoryManager extends ExtensionManager<IFeatureModelFactory> {

	public static IFactoryWorkspaceProvider factoryWorkspaceProvider = new CoreFactoryWorkspaceProvider();

	private FMFactoryManager() {
		setExtensionLoaderInternal(new CoreExtensionLoader<IFeatureModelFactory>(DefaultFeatureModelFactory.class, ExtendedFeatureModelFactory.class));
	}

	private static FMFactoryManager instance = new FMFactoryManager();

	public static FMFactoryManager getInstance() {
		return instance;
	}

	public static void setExtensionLoader(IExtensionLoader<IFeatureModelFactory> extensionLoader) {
		instance.setExtensionLoaderInternal(extensionLoader);
	}

	public static void addFactoryWorkspace(String path, FactoryWorkspace workspace) {
		factoryWorkspaceProvider.addFactoryWorkspace(path, workspace);
	}

	/**
	 * Returns a specific factory associated with the string <b>id</b>. By default, the following factories are available: <ul>
	 * <li><b>de.ovgu.featureide.fm.core.DefaultFeatureModelFactory</b>: An instance of {@link DefaultFeatureModelFactory}</li>
	 * <li><b>de.ovgu.featureide.fm.core.ExtendedFeatureModelFactory</b>: An instance of {@link ExtendedFeatureModelFactory}</li> </ul>
	 *
	 * @param id the (unique) identifier for an instance of {@link IFeatureModelFactory} to be returned
	 * @return Returns Instance of feature model factory associated with <b>id</b>, or throws <b<>RuntimeException</b> in case <b>id</b> is not known
	 * @throws NoSuchFactoryException If no factory with the given ID is registered.
	 */
	public static IFeatureModelFactory getFactoryById(String id) throws NoSuchExtensionException {
		return instance.getExtension(id);
	}

	public static void setDefaultFactory(String id) throws NoSuchExtensionException {
		factoryWorkspaceProvider.getFactoryWorkspace().setDefaultFactoryID(id);
	}

	public static FactoryWorkspace getFactoryWorkspace() {
		return factoryWorkspaceProvider.getFactoryWorkspace();
	}

	public static FactoryWorkspace getFactoryWorkspace(String path) {
		return factoryWorkspaceProvider.getFactoryWorkspace(path);
	}

	/**
	 * Returns the feature model factory that was used to create the given model. (if the factory is not available the default factory is returned).
	 *
	 * @param featureModel the feature model
	 *
	 * @return Returns the feature model factory for the given feature model.
	 */
	public static IFeatureModelFactory getFactory(IFeatureModel featureModel) {
		try {
			return getFactoryById(featureModel.getFactoryID());
		} catch (final NoSuchExtensionException e) {
			Logger.logError(e);
			return DefaultFeatureModelFactory.getInstance();
		}
	}

	/**
	 * Return the currently set default factory (if not changed, it is an instance of the built-in {@link DefaultFeatureModelFactory}).<br/> <br/> <b>Important
	 * Note:</b> If possible, use {@link #getFactory(String, IPersistentFormat)} or {@link #getFactory(IFeatureModel)} instead to ensure that the correct
	 * factory is used for the underlying feature model file.
	 *
	 * @return Returns the default feature model factory.
	 */
	public static IFeatureModelFactory getDefaultFactory() {
		try {
			return getFactoryById(factoryWorkspaceProvider.getFactoryWorkspace().getDefaultFactoryID());
		} catch (final NoSuchExtensionException e) {
			Logger.logError(e);
			return DefaultFeatureModelFactory.getInstance();
		}
	}

	/**
	 * Returns the currently set default factory for the given path (if none is specified an instance of the default factory is returned).<br/> <br/>
	 * <b>Important Note:</b> If possible, use {@link #getFactory(String, IPersistentFormat)} or {@link #getFactory(IFeatureModel)} instead to ensure that the
	 * correct factory is used for the underlying feature model file.
	 *
	 * @param path
	 *
	 * @return Returns the default feature model factory for a certain path.
	 *
	 * @throws NoSuchExtensionException
	 */
	public static IFeatureModelFactory getDefaultFactoryForPath(String path) throws NoSuchExtensionException {
		return getFactoryById(factoryWorkspaceProvider.getFactoryWorkspace(path).getDefaultFactoryID());
	}

	/**
	 * Returns the feature model factory for the given path and format. (if none is specified an instance of the default factory is returned).
	 *
	 * @param path
	 * @param format
	 *
	 * @return Returns the feature model factory for a certain path and format.
	 *
	 * @throws NoSuchExtensionException
	 */
	public static IFeatureModelFactory getFactory(String path, IPersistentFormat<IFeatureModel> format) throws NoSuchExtensionException {
		return getFactoryById(factoryWorkspaceProvider.getFactoryWorkspace(path).getID(format));
	}

	/**
	 * Returns the currently set default factory for the given format (if none is specified an instance of the default factory is returned).<br/> <br/>
	 * <b>Important Note:</b> If possible, use {@link #getFactory(String, IPersistentFormat<IFeatureModel>)} or {@link #getFactory(IFeatureModel)} instead to
	 * ensure that the correct factory is used for the underlying feature model file.
	 *
	 * @param format
	 *
	 * @return Returns the default feature model factory for a certain format.
	 *
	 * @throws NoSuchExtensionException
	 */
	public static IFeatureModelFactory getDefaultFactoryForFormat(IPersistentFormat<IFeatureModel> format) throws NoSuchExtensionException {
		return getFactoryById(factoryWorkspaceProvider.getFactoryWorkspace().getID(format));
	}

	/**
	 * @return An empty feature model from the default factory.
	 */
	public static IFeatureModel getEmptyFeatureModel() {
		return getDefaultFactory().createFeatureModel();
	}

}
