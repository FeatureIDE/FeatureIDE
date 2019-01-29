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

import java.nio.file.Path;

import de.ovgu.featureide.fm.core.IExtensionLoader;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFactory;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Returns custom factories to create {@link IFeatureModel}, {@link IFeature}, and {@link IConstraint} instances.
 *
 * @author Sebastian Krieter
 */
public final class FMFactoryManager extends FactoryManager<IFeatureModel> {

	/**
	 * Return the currently set default factory (if not changed, it is an instance of the built-in {@link DefaultFeatureModelFactory}).<br> <br> <b>Important
	 * Note:</b> If possible, use {@link #getFactory(String, IPersistentFormat)} or {@link #getFactory(IFeatureModel)} instead to ensure that the correct
	 * factory is used for the underlying feature model file.
	 *
	 * @return Returns the ID of the default feature model factory.
	 */
	@Override
	protected String getDefaultID() {
		return DefaultFeatureModelFactory.ID;
	}

	@Override
	protected Class<?>[] getDefaultClasses() {
		return new Class<?>[] { DefaultFeatureModelFactory.class, ExtendedFeatureModelFactory.class };
	}

	private static FMFactoryManager instance = new FMFactoryManager();

	public static FMFactoryManager getInstance() {
		instance.setLoader(null, null);
		return instance;
	}

	public static void initialize(IExtensionLoader<IFactory<IFeatureModel>> extensionLoader, IFactoryWorkspaceLoader factorySpaceLoader) {
		instance.setLoader(extensionLoader, factorySpaceLoader);
	}

	/**
	 * Returns the feature model factory that was used to create the given model. (if the factory is not available the default factory is returned).
	 *
	 * @param featureModel the feature model
	 *
	 * @return Returns the feature model factory for the given feature model.
	 */
	@Override
	public IFeatureModelFactory getFactory(IFeatureModel object) {
		try {
			return getFactory(object.getFactoryID());
		} catch (final NoSuchExtensionException e) {
			Logger.logError(e);
			return DefaultFeatureModelFactory.getInstance();
		}
	}

	@Override
	public IFeatureModelFactory getFactory(String id) throws NoSuchExtensionException {
		return (IFeatureModelFactory) super.getFactory(id);
	}

	@Override
	public IFeatureModelFactory getFactory(Path path, IPersistentFormat<? extends IFeatureModel> format) throws NoSuchExtensionException {
		return (IFeatureModelFactory) super.getFactory(path, format);
	}

	@Override
	public IFeatureModelFactory getFactory(IPersistentFormat<? extends IFeatureModel> format) throws NoSuchExtensionException {
		return (IFeatureModelFactory) super.getFactory(format);
	}

	@Override
	public boolean addExtension(IFactory<IFeatureModel> extension) {
		return (extension instanceof IFeatureModelFactory) ? super.addExtension(extension) : false;
	}

}
