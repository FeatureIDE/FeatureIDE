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

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.APersistentFormat;

/**
 * TODO description
 *
 * @author liuya
 */
public class LatexFormat extends APersistentFormat<Configuration> {

	public static final String ID = PluginID.PLUGIN_ID + "format.fm" + LatexFormat.class.getSimpleName();

	@Override
	public String write(Configuration object) {
		return "Hello beautiful World!";
	}

	@Override
	public boolean supportsRead() {
		return false;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getSuffix() {
		// TODO Auto-generated method stub
		return ".tex";
	}

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return "LaTeX Document";
	}

	@Override
	public String getId() {
		// TODO Auto-generated method stub
		return ID;
	}

}
