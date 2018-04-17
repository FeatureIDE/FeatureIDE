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
import javax.annotation.Nonnull;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.XMLConfFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Responsible to load and save all information for a feature model instance.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationManager extends AFileManager<Configuration> {

	private static class ObjectCreator extends AFileManager.ObjectCreator<Configuration> {

		private final Configuration configuration;

		public ObjectCreator(Configuration configuration) {
			super(Configuration.class, ConfigurationManager.class, ConfigFormatManager.getInstance());
			this.configuration = configuration;
		}

		@Override
		protected Configuration createObject(Path path, IPersistentFormat<Configuration> format) throws NoSuchExtensionException {
			return configuration;
		}
	}

	@Nonnull
	public static IPersistentFormat<Configuration> getDefaultFormat() {
		return new XMLConfFormat();
	}

	@CheckForNull
	public static ConfigurationManager getInstance(Path path) {
		return AFileManager.getInstance(path, new ObjectCreator(null), false);
	}

	@CheckForNull
	public static ConfigurationManager getInstance(Path path, Configuration configuration) {
		return AFileManager.getInstance(path, new ObjectCreator(configuration), true);
	}

	public static FileHandler<Configuration> load(Path path, Configuration configuration) {
		return AFileManager.getFileHandler(path, new ObjectCreator(configuration));
	}

	protected ConfigurationManager(Configuration configuration, FileIdentifier<Configuration> identifier) {
		super(configuration, identifier);
	}

	@Override
	protected Configuration copyObject(Configuration oldObject) {
		return oldObject.clone();
	}

	public void setConfiguration(Configuration configuration) {
		variableObject = configuration;
		synchronized (syncObject) {
			// persistentObject = copyObject(variableObject);
			setPersistentObject(copyObject(variableObject));
		}
	}

}
