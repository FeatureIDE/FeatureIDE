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

import java.nio.file.Path;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
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

	public static final int CHANGE_ALL = 0;
	public static final int CHANGE_FEATURES = 1;
	public static final int CHANGE_MANUAL = 2;
	public static final int CHANGE_AUTOMATIC = 3;
	public static final int CHANGE_CONFIGURABLE_ATTRIBUTE = 4;
	public static final int CHANGE_NOTHING = Integer.MAX_VALUE;

	@CheckForNull
	public static ConfigurationManager getInstance(Path path) {
		return getOrCreateInstance(path, ConfigurationManager.class, null);
	}

	public static boolean isFileSupported(Path filePath) {
		return ConfigFormatManager.getInstance().hasFormat(filePath);
	}

	public static final Configuration load(Path path) {
		return ConfigurationIO.getInstance().load(path);
	}

	public static FileHandler<Configuration> getFileHandler(Path path) {
		return ConfigurationIO.getInstance().getFileHandler(path);
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

	private IFeatureModelManager featureModelManager;

	public void linkFeatureModel(IFeatureModelManager featureModelManager) {
		fileOperationLock.lock();
		try {
			if ((featureModelManager == null) || (this.featureModelManager != featureModelManager)) {
				this.featureModelManager = featureModelManager;
				final FeatureModelFormula formula = featureModelManager.getPersistentFormula();
				getObject().updateFeatures(formula);
				getVarObject().updateFeatures(formula);
			}
		} finally {
			fileOperationLock.unlock();
		}
	}

	public IFeatureModelManager getFeatureModelManager() {
		return featureModelManager;
	}

	public void update() {
		if (featureModelManager != null) {
			final FeatureModelFormula formula = featureModelManager.getPersistentFormula();
			fileOperationLock.lock();
			try {
				getObject().updateFeatures(formula);
				final Configuration configuration = getVarObject();
				configuration.updateFeatures(formula);
			} finally {
				fileOperationLock.unlock();
			}
		}
	}

	@Override
	protected Configuration createObject() throws Exception {
		final Configuration configuration = super.createObject();
		if (featureModelManager != null) {
			configuration.updateFeatures(featureModelManager.getPersistentFormula());
		}
		return configuration;
	}

}
