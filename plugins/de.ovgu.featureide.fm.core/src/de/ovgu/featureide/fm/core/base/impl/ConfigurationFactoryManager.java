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

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IConfigurationFactory;
import de.ovgu.featureide.fm.core.base.IFactory;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Manages all factories for configuration objects.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationFactoryManager extends FactoryManager<Configuration> {

	@Override
	protected String getDefaultID() {
		return DefaultConfigurationFactory.ID;
	}

	private static ConfigurationFactoryManager instance = new ConfigurationFactoryManager();

	public static ConfigurationFactoryManager getInstance() {
		return instance;
	}

	/**
	 * Returns the configuration factory that was used to create the given configuration. (if the factory is not available the default factory is returned).
	 *
	 * @param configuration the configuration
	 *
	 * @return Returns the configuration factory for the given configuration.
	 */
	@Override
	public IConfigurationFactory getFactory(Configuration configuration) {
		try {
			return getFactory(configuration.getFactoryID());
		} catch (final NoSuchExtensionException e) {
			Logger.logError(e);
			return DefaultConfigurationFactory.getInstance();
		}
	}

	@Override
	public IConfigurationFactory getFactory(String id) throws NoSuchExtensionException {
		return (IConfigurationFactory) super.getFactory(id);
	}

	@Override
	public IConfigurationFactory getFactory(Path path, IPersistentFormat<? extends Configuration> format) throws NoSuchExtensionException {
		return (IConfigurationFactory) super.getFactory(path, format);
	}

	@Override
	public IConfigurationFactory getFactory(IPersistentFormat<? extends Configuration> format) throws NoSuchExtensionException {
		return (IConfigurationFactory) super.getFactory(format);
	}

	@Override
	public boolean addExtension(IFactory<Configuration> extension) {
		return (extension instanceof IConfigurationFactory) ? super.addExtension(extension) : false;
	}

}
