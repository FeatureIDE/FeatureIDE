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

import de.ovgu.featureide.fm.core.IExtensionLoader;
import de.ovgu.featureide.fm.core.configuration.DefaultFormat;
import de.ovgu.featureide.fm.core.configuration.EquationFormat;
import de.ovgu.featureide.fm.core.configuration.ExpressionFormat;
import de.ovgu.featureide.fm.core.configuration.FeatureIDEFormat;
import de.ovgu.featureide.fm.core.configuration.XMLConfFormat;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;

/**
 * Manages all formats for {@link de.ovgu.featureide.fm.core.configuration.Configuration configurations}.
 *
 * @author Sebastian Krieter
 */
public final class ConfigFormatManager extends FormatManager<IConfigurationFormat> {

	private ConfigFormatManager() {
		super(XMLConfFormat.class, DefaultFormat.class, FeatureIDEFormat.class, EquationFormat.class, ExpressionFormat.class);
	}

	private static ConfigFormatManager instance = new ConfigFormatManager();

	public static ConfigFormatManager getInstance() {
		return instance;
	}

	public static void setExtensionLoader(IExtensionLoader<IConfigurationFormat> extensionLoader) {
		instance.setExtensionLoaderInternal(extensionLoader);
	}

	public static IConfigurationFormat getDefaultFormat() {
		return new XMLConfFormat();
	}

}
