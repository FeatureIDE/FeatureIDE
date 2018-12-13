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

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.base.impl.ConfigurationFactoryManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Responsible to load and save all information for a feature model instance.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationManager extends AFileManager<Configuration> {

	@CheckForNull
	public static ConfigurationManager getInstance(Path path) {
		return getInstance(path, true);
	}

	@CheckForNull
	public static final ConfigurationManager getInstance(Path identifier, boolean createInstance) {
		return getInstance(identifier, createInstance, ConfigurationManager.class);
	}

	public static final Configuration load(Path path) {
		return ConfigurationIO.getInstance().load(path);
	}

	public static final boolean save(Configuration configuration, Path path, IPersistentFormat<Configuration> format) {
		return ConfigurationIO.getInstance().save(configuration, path, format);
	}

	protected ConfigurationManager(Path identifier) {
		super(identifier, ConfigFormatManager.getInstance(), ConfigurationFactoryManager.getInstance());
	}

	@Override
	public IConfigurationFormat getFormat() {
		return (IConfigurationFormat) super.getFormat();
	}

	@Override
	protected Configuration copyObject(Configuration oldObject) {
		return oldObject.clone();
	}

	private FeatureModelManager featureModelManager;

	public void linkFeatureModel(FeatureModelManager featureModelManager) {
		this.featureModelManager = featureModelManager;
		final IFeatureModel featureModel = featureModelManager.getObject();
		fileOperationLock.lock();
		try {
			getObject().initFeatures(featureModel);
			editObject().initFeatures(featureModel);
		} finally {
			fileOperationLock.unlock();
		}
	}

	public void update() {
		if (featureModelManager != null) {
			final IFeatureModel featureModel = featureModelManager.getObject();
			fileOperationLock.lock();
			try {
				getObject().updateFeatures(featureModel);
				final Configuration configuration = editObject();
				configuration.updateFeatures(featureModel);
				configuration.update();
			} finally {
				fileOperationLock.unlock();
			}
		}
	}

	@Override
	protected Configuration createObject() throws Exception {
		final Configuration configuration = super.createObject();
		configuration.setPropagate(true);
		if (featureModelManager != null) {
			configuration.initFeatures(featureModelManager.getObject());
		}
		return configuration;
	}

}
