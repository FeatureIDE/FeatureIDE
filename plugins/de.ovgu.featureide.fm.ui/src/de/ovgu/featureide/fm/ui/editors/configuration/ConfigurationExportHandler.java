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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.nio.file.Path;
import java.util.List;

import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationIO;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.ui.handlers.AExportHandler;

/**
 * Handler for exporting configurations as regular or extended configuration
 *
 * @author Chico Sundermann
 */
public class ConfigurationExportHandler extends AExportHandler<Configuration> {

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.handlers.AExportHandler#getFormats()
	 */
	@Override
	protected List<? extends IPersistentFormat<Configuration>> getFormats() {
		return ConfigFormatManager.getInstance().getExtensions();
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.handlers.AExportHandler#read(java.nio.file.Path)
	 */
	@Override
	protected FileHandler<Configuration> read(Path configurationFilePath) {
		return ConfigurationIO.getInstance().getFileHandler(configurationFilePath);
	}

}
