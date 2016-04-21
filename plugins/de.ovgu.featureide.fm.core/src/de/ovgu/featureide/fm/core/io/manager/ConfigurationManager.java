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
package de.ovgu.featureide.fm.core.io.manager;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.DefaultFormat;
import de.ovgu.featureide.fm.core.configuration.FeatureIDEFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Responsible to load and save all information for a feature model instance.
 * 
 * @author Sebastian Krieter
 */
public class ConfigurationManager extends AFileManager<Configuration> {

	public static enum FormatType implements IFormatType<Configuration> {
		XML_FIDE(StringTable.CONF, DefaultFormat.class), CONFIG(StringTable.CONFIG, DefaultFormat.class),
		EQUATION(StringTable.EQUATION, DefaultFormat.class), FIDECONF(StringTable.FIDECONF, FeatureIDEFormat.class);

		private final String suffix;
		private final Class<? extends IPersistentFormat<Configuration>> format;

		private FormatType(String suffix, Class<? extends IPersistentFormat<Configuration>> format) {
			this.suffix = suffix;
			this.format = format;
		}

		@Override
		public String getSuffix() {
			return suffix;
		}

		@Override
		public Class<? extends IPersistentFormat<Configuration>> getFormat() {
			return format;
		}
	}

	public static IPersistentFormat<Configuration> getDefaultFormat() {
		return new DefaultFormat();
	}

	public static IPersistentFormat<Configuration> getFormat(FormatType formatType) {
		try {
			return formatType.getFormat().newInstance();
		} catch (InstantiationException | IllegalAccessException e) {
			throw new RuntimeException();
		}
	}

	@CheckForNull
	public static IPersistentFormat<Configuration> getFormat(String fileName) {
		return AFileManager.<Configuration> getFormat(fileName, FormatType.values());
	}

	public static ConfigurationManager getInstance(Configuration configuration, String absolutePath) {
		return getInstance(configuration, absolutePath, getFormat(absolutePath));
	}

	public static ConfigurationManager getInstance(Configuration configuration, String absolutePath, IPersistentFormat<Configuration> format) {
		final ConfigurationManager instance = FileManagerMap.getInstance(configuration, absolutePath, format, ConfigurationManager.class, Configuration.class);
		instance.read();
		return instance;
	}

	protected ConfigurationManager(Configuration configuration, String absolutePath, IPersistentFormat<Configuration> modelHandler) {
		super(configuration, absolutePath, modelHandler);
	}

	@Override
	protected Configuration copyObject(Configuration oldObject) {
		return oldObject.clone();
	}

	public void setConfiguration(Configuration configuration) {
		variableObject = configuration;
		persist();
	}

}
