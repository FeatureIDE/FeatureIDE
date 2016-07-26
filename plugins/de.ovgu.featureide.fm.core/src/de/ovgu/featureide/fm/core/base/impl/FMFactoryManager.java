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
package de.ovgu.featureide.fm.core.base.impl;

import de.ovgu.featureide.fm.core.CoreExtensionLoader;
import de.ovgu.featureide.fm.core.ExtensionManager;
import de.ovgu.featureide.fm.core.IExtensionLoader;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.velvet.SimpleVelvetFeatureModelFormat;

/**
 * Returns custom factories to create {@link IFeatureModel}, {@link IFeature}, and {@link IConstraint} instances.
 * 
 * @author Sebastian Krieter
 */
public final class FMFactoryManager extends ExtensionManager<IFeatureModelFactory> {

	public static IFactoryWorkspaceProvider factoryWorkspaceProvider = new CoreFactoryWorkspaceProvider();

	private FMFactoryManager() {
		setExtensionLoaderInternal(new CoreExtensionLoader<>(new DefaultFeatureModelFactory(), new ExtendedFeatureModelFactory()));
		factoryWorkspaceProvider.getFactoryWorkspace().assignID(SimpleVelvetFeatureModelFormat.ID, ExtendedFeatureModelFactory.ID);
	}

	private static FMFactoryManager instance = new FMFactoryManager();

	private static IFeatureModelFactory defaultFactory = DefaultFeatureModelFactory.getInstance();

	public static FMFactoryManager getInstance() {
		return instance;
	}

	public static void setExtensionLoader(IExtensionLoader<IFeatureModelFactory> extensionLoader) {
		instance.setExtensionLoaderInternal(extensionLoader);
	}

	/**
	 * Returns a specific factory associated with the string <b>id</b>. By default, the following
	 * factories are available:
	 * <ul>
	 * <li><b>de.ovgu.featureide.fm.core.DefaultFeatureModelFactory</b>: An instance of {@link DefaultFeatureModelFactory}</li>
	 * <li><b>de.ovgu.featureide.fm.core.ExtendedFeatureModelFactory</b>: An instance of {@link ExtendedFeatureModelFactory}</li>
	 * </ul>
	 * 
	 * @param id the (unique) identifier for an instance of {@link IFeatureModelFactory} to be returned
	 * @return Returns Instance of feature model factory associated with <b>id</b>, or throws <b<>RuntimeException</b> in case <b>id</b> is not known
	 * @throws NoSuchFactoryException If no factory with the given ID is registered.
	 */
	public static IFeatureModelFactory getFactoryById(String id) throws NoSuchExtensionException {
		return instance.getExtension(id);
	}

	public static void setDefaultFactory(String id) throws NoSuchExtensionException {
		defaultFactory = getFactoryById(id);
		factoryWorkspaceProvider.getFactoryWorkspace().setDefaultFactoryID(defaultFactory.getId());
	}

	public static FactoryWorkspace getFactoryWorkspace() {
		return factoryWorkspaceProvider.getFactoryWorkspace();
	}

	public static FactoryWorkspace getFactoryWorkspace(String path) {
		return factoryWorkspaceProvider.getFactoryWorkspace(path);
	}

	/**
	 * @return Returns the default instance of the built-in {@link DefaultFeatureModelFactory} which provides access to the default {@link IFeatureModel} and
	 *         {@link IFeature} implementations of FeatureIDE
	 */
	public static IFeatureModelFactory getFactory() {
		return defaultFactory;
	}

	public static IFeatureModelFactory getFactory(String path) throws NoSuchExtensionException {
		return getFactoryById(factoryWorkspaceProvider.getFactoryWorkspace(path).getDefaultFactoryID());
	}

	public static IFeatureModelFactory getFactory(String path, IFeatureModelFormat format) throws NoSuchExtensionException {
		return getFactoryById(factoryWorkspaceProvider.getFactoryWorkspace(path).getID(format));
	}

	public static IFeatureModelFactory getFactory(IFeatureModelFormat format) throws NoSuchExtensionException {
		return getFactoryById(factoryWorkspaceProvider.getFactoryWorkspace().getID(format));
	}

}
